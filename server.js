'use strict';
/**
 * Nova Browser - 本地渲染代理服务
 *
 * 让"网页版浏览器"能真正加载第三方网站：
 *  - 剥离 X-Frame-Options / CSP 等响应头，解除 iframe 嵌套限制
 *  - HTML 重写：注入 <base> 与运行时接管脚本
 *  - 运行时接管：页面内的 fetch / XHR / sendBeacon / EventSource / WebSocket
 *    全部重写到代理，解决跨域 CORS 导致的"页面出来但内容空白"
 *  - Cookie：服务端 Jar 按主域隔离，与页面内 document.cookie shim 双向同步
 *  - 非 HTML 资源（视频/图片/JS/CSS）流式透传，保留 Range 分段，视频可拖动进度
 *  - 动态创建的 iframe 也重写到代理
 */

const http = require('http');
const https = require('https');
const zlib = require('zlib');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { URL } = require('url');

const ROOT = __dirname;
const BASE_PORT = Number(process.env.PORT || 7180);
const UA =
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';
/* 哔哩哔哩 App（安卓 WebView）UA：手机端访问 *.bilibili.com 时模拟，
 * 站点会按 App/H5 移动版输出（番剧 m 站 H5 播放器，播放体验更好） */
const BILI_APP_UA =
  'Mozilla/5.0 (Linux; Android 14; 2210132C Build/UKQ1.230917.001; wv) AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/126.0.0.0 Mobile Safari/537.36 bilibili_android/7730300';

/* ------------------------------------------------------------------ *
 * 公网模式护栏
 *
 * 部署到公网后，本服务就是一个"人人可用的抓取代理"，必须自带防护：
 *   - SSRF 防护：禁止代理到回环 / 内网 / 链路本地 / 云元数据地址，
 *     并在 DNS 解析层过滤（防止用域名指向内网绕过）
 *   - 频率限制：按来源 IP 限流，避免被当成公共翻墙/爬虫出口滥用
 *
 * 触发条件：云平台会注入 PORT 环境变量，或显式 NOVA_PUBLIC=1。
 * 本地直跑（无 PORT、无 NOVA_PUBLIC）保持原行为不变，
 * 这样"用浏览器访问局域网内设备"这类本地用法不受影响。
 * 需要强制关闭：NOVA_PUBLIC=0
 * ------------------------------------------------------------------ */
const PUBLIC_MODE =
  process.env.NOVA_PUBLIC === '1' ||
  (!!process.env.PORT && process.env.NOVA_PUBLIC !== '0');
const RATE_WINDOW_MS = 60 * 1000;
const RATE_MAX = Number(process.env.NOVA_RATE_MAX || 1500); // 每 IP 每分钟请求数上限
/* 单个页面往往要拉几百个子资源，阈值放宽；主要拦截的是"被当成 API 刷"的场景 */

function isPrivateIp(addr) {
  const ip = String(addr || '').trim().toLowerCase().replace(/^\[|\]$/g, '');
  if (!ip) return true;
  /* IPv6 */
  if (ip.includes(':')) {
    if (ip === '::1' || ip === '::') return true;
    const mapped = /^::ffff:(\d+\.\d+\.\d+\.\d+)$/.exec(ip);
    if (mapped) return isPrivateIp(mapped[1]);
    if (/^f[cd][0-9a-f]{2}:/.test(ip)) return true;   // fc00::/7 唯一本地
    if (/^fe[89ab][0-9a-f]:/.test(ip)) return true;   // fe80::/10 链路本地
    return false;
  }
  const m = /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.exec(ip);
  if (!m) return false;
  const a = +m[1], b = +m[2];
  if (a === 0 || a === 10 || a === 127) return true;
  if (a === 169 && b === 254) return true;            // 云元数据 169.254.169.254
  if (a === 172 && b >= 16 && b <= 31) return true;
  if (a === 192 && b === 168) return true;
  if (a === 100 && b >= 64 && b <= 127) return true;  // 运营商级 NAT
  if (a >= 224) return true;                          // 组播 / 保留
  return false;
}

/* 已知的云元数据 / 内部主机名 */
const BLOCKED_HOSTNAMES = new Set([
  'metadata.google.internal',
  'metadata.goog',
  'instance-data',
  'metadata',
]);

/* 解析阶段拦截：域名解析出来的地址若落在内网，直接拒连。
 * 同时把校验过的地址交给连接使用，避免"校验后重解析"的 DNS rebinding。 */
function safeLookup(hostname, opts, cb) {
  const dns = require('dns');
  dns.lookup(hostname, { all: true, verbatim: true }, (err, addrs) => {
    if (err) return cb(err);
    const list = Array.isArray(addrs) ? addrs : [addrs];
    const ok = list.filter((a) => a && !isPrivateIp(a.address));
    if (!ok.length) {
      const e = new Error('目标地址属于内网/保留网段，已拒绝');
      e.code = 'ENOVA_BLOCKED';
      return cb(e);
    }
    if (opts && opts.all) return cb(null, ok.map((a) => ({ address: a.address, family: a.family })));
    return cb(null, ok[0].address, ok[0].family);
  });
}

/* 字面量拦截：URL 里直接写内网 IP / 本地域名的，连解析都不用做 */
function blockedTargetSync(u) {
  const h = String(u.hostname || '').toLowerCase().replace(/^\[|\]$/g, '');
  if (!h) return '地址为空';
  if (BLOCKED_HOSTNAMES.has(h)) return '目标为云元数据地址';
  if (/\.local$/.test(h) || /\.internal$/.test(h) || h === 'localhost' || /\.localhost$/.test(h)) {
    return '目标为内网地址';
  }
  if (/^[\d.]+$/.test(h) && isPrivateIp(h)) return '目标为内网/保留网段地址';
  if (h.includes(':') && isPrivateIp(h)) return '目标为内网/保留网段地址';
  return null;
}

/* 简易令牌桶：每 IP 每分钟 N 次 */
const rateBuckets = new Map();
function rateLimited(ip) {
  const now = Date.now();
  const b = rateBuckets.get(ip);
  if (!b || now > b.resetAt) {
    rateBuckets.set(ip, { count: 1, resetAt: now + RATE_WINDOW_MS });
    if (rateBuckets.size > 5000) {
      for (const [k, v] of rateBuckets) if (now > v.resetAt) rateBuckets.delete(k);
    }
    return false;
  }
  b.count += 1;
  return b.count > RATE_MAX;
}

function clientIpOf(req) {
  const xf = String(req.headers['x-forwarded-for'] || '').split(',')[0].trim();
  return xf || (req.socket && req.socket.remoteAddress) || 'unknown';
}

/* 每个客户端最近一次代理的真实站点 origin：站点页面内未被钩住且不带
 * Referer 的跳转（location.href='/xxx' + no-referrer 策略）会以裸路径打到
 * 本服务，兜底 302 需要知道该回哪个站点。 */
const LAST_ORIGIN = new Map(); // ip -> { origin, t }
const LAST_ORIGIN_TTL = 30 * 60 * 1000;

function rememberLastOrigin(req, u) {
  try {
    const ip = clientIpOf(req);
    LAST_ORIGIN.set(ip, { origin: u.origin, t: Date.now() });
    if (LAST_ORIGIN.size > 5000) {
      const now = Date.now();
      for (const [k, v] of LAST_ORIGIN) { if (now - v.t > LAST_ORIGIN_TTL) LAST_ORIGIN.delete(k); }
    }
  } catch (e) { /* ignore */ }
}

/* ------------------------------------------------------------------ *
 * Cookie Jar（按主域隔离，服务端保存）
 * ------------------------------------------------------------------ */
const jar = new Map(); // baseDomain -> Map(name -> value)

const MULTI_TLD = new Set([
  'com.cn', 'net.cn', 'org.cn', 'gov.cn', 'edu.cn', 'ac.cn',
  'co.uk', 'org.uk', 'ac.uk', 'gov.uk',
  'com.hk', 'com.tw', 'com.jp', 'com.au', 'com.sg', 'com.kr', 'co.kr', 'co.jp',
]);

function baseDomainOf(host) {
  let h = String(host || '').toLowerCase().replace(/^www\./, '');
  const parts = h.split('.').filter(Boolean);
  if (parts.length <= 2) return parts.join('.');
  const two = parts.slice(-2).join('.');
  if (MULTI_TLD.has(two)) return parts.slice(-3).join('.');
  return two;
}
function jarOf(base) {
  if (!jar.has(base)) jar.set(base, new Map());
  return jar.get(base);
}
function cookieHeaderFor(host) {
  const j = jarOf(baseDomainOf(host));
  if (!j.size) return '';
  return [...j.entries()].map(([k, v]) => k + '=' + v).join('; ');
}
/* Cookie 归属罐子：优先遵循 Set-Cookie 的 Domain 属性（浏览器规则：
 * Domain 必须是请求 host 的后缀，否则拒绝），否则按请求 host 的主域归并。 */
function jarKeyFor(host, domainAttr) {
  const h = String(host || '').toLowerCase().replace(/^\./, '');
  if (domainAttr) {
    const d = String(domainAttr).toLowerCase().replace(/^\./, '');
    if (d && (h === d || h.endsWith('.' + d))) return baseDomainOf(d);
  }
  return baseDomainOf(h);
}
function parseSetCookie(raw) {
  const parts = String(raw).split(';');
  const eq = parts[0].indexOf('=');
  if (eq <= 0) return null;
  const name = parts[0].slice(0, eq).trim();
  const value = parts[0].slice(eq + 1).trim();
  if (!name) return null;
  let dead = false;
  let domain = '';
  for (let i = 1; i < parts.length; i++) {
    const s = parts[i].trim();
    const li = s.indexOf('=');
    const k = (li < 0 ? s : s.slice(0, li)).trim().toLowerCase();
    const v = li < 0 ? '' : s.slice(li + 1).trim();
    if (k === 'max-age' && Number(v) <= 0) dead = true;
    if (k === 'expires') {
      const d = Date.parse(v);
      if (!isNaN(d) && d < Date.now()) dead = true;
    }
    if (k === 'domain') domain = v;
  }
  return { name, value, dead, domain };
}
/* 风控验证通过令牌 x5sec 有时不走 Set-Cookie，而是放在 bx-x5sec / bx-x5sec-root
 * 响应头里，由验证码页 JS 自己 document.cookie 写入。代理环境下这段写入可能因跨 frame
 * 时序或域名不匹配而丢失，这里在服务端直接兜底落罐：验证通过 → 凭证在罐里 → 重试请求带上。 */
function captureRiskCookies(host, headers) {
  if (!headers) return;
  for (const key of ['bx-x5sec', 'bx-x5sec-root']) {
    const raw = headers[key];
    if (!raw) continue;
    const items = Array.isArray(raw) ? raw : [raw];
    for (const s of items) {
      const t = String(s);
      if (!/(^|;)\s*x5sec\s*=/i.test(t)) continue;
      const c = parseSetCookie(t.replace(/^[\s;]+/, ''));
      if (!c || !/^x5sec$/i.test(c.name)) continue;
      const j = jarOf(jarKeyFor(host, c.domain));
      if (c.dead) j.delete(c.name); else j.set(c.name, c.value);
      try { diag({ riskck: c.name, from: host, len: String(c.value).length }); } catch (e) { /* ignore */ }
    }
  }
}
function storeCookies(host, list) {
  if (!list) return;
  const items = Array.isArray(list) ? list : [list];
  for (const raw of items) {
    const c = parseSetCookie(raw);
    if (!c) continue;
    const j = jarOf(jarKeyFor(host, c.domain));
    if (c.dead) j.delete(c.name);
    else j.set(c.name, c.value);
  }
}

/* ------------------------------------------------------------------ *
 * 诊断日志：NOVA_DIAG=1 时记录代理请求/响应（Cookie 仅记名不记值）
 * 用于排查风控类问题（验证码反复出现等）
 * ------------------------------------------------------------------ */
const DIAG = process.env.NOVA_DIAG === '1';
const DIAG_FILE = path.join(ROOT, 'nova-diag.log');
function ckNames(header) {
  return String(header || '')
    .split(';')
    .map((s) => s.trim().split('=')[0])
    .filter(Boolean)
    .slice(0, 40);
}
function setCkNames(list) {
  if (!list) return [];
  const a = Array.isArray(list) ? list : [list];
  return a.map((s) => String(s).split(';')[0].split('=')[0]).filter(Boolean);
}
let diagSize = 0;
const DIAG_MAX = 5 * 1024 * 1024;
function diag(entry) {
  if (!DIAG || diagSize > DIAG_MAX) return;
  try {
    const line = JSON.stringify(Object.assign({ t: new Date().toISOString() }, entry)) + '\n';
    diagSize += Buffer.byteLength(line);
    fs.appendFileSync(DIAG_FILE, line);
  } catch (e) { /* ignore */ }
}

/* ------------------------------------------------------------------ *
 * /__ck 访问令牌：页面 JS 只能同步"自己站点"的 Cookie，防跨站读取
 * ------------------------------------------------------------------ */
const SECRET = crypto.randomBytes(24).toString('hex');
function ckToken(realUrl) {
  return crypto.createHmac('sha256', SECRET).update(String(realUrl)).digest('base64url').slice(0, 24);
}

/* ------------------------------------------------------------------ *
 * 注入到每个被代理页面中的运行时接管脚本
 * ------------------------------------------------------------------ */
function buildInjectScript(realUrl) {
  const u = new URL(realUrl);
  const origin = u.origin;
  const token = ckToken(realUrl);

  return [
    '<script data-nova="1">(function(){',
    'var ORIGIN=' + JSON.stringify(origin) + ';',
    'var CKT=' + JSON.stringify(token) + ';',
    /* 令牌按完整真实 URL 计算，/__ck 必须上报同一字符串，否则服务端 ckToken(o) 校验必然 403 */
    'var RU=' + JSON.stringify(realUrl) + ';',
    'var PROXY=location.origin;',
    /* 哔哩哔哩"外链播放器→视频页"提升：player.html 被服务端 302 成视频页时 URL 带 _nova_p2v=1。
     * 此时页面嵌在卡片页的隐藏小 iframe 里，用户看不到；且壳 iframe 会触发 B 站嵌入检测
     * 把视频页降级为"立即播放"卡页（死循环）。shell 与页面同源，这里把顶层导航到
     * 带 p2v 标记的裸视频页（服务端对 p2v 的顶层 document 请求直接放行，顶层全屏可播）。 */
    'try{',
    '  if(RU.indexOf("_nova_p2v=1")>=0&&window.top!==window.self){',
    '    var __u2=new URL(RU);',
    '    var __p2u=__u2.pathname+(__u2.search||"?")+"&__nova_url="+encodeURIComponent(RU);',
    '    var __done=false;',
    '    try{top.location.replace(__p2u);__done=true;}catch(e){}',
    '    if(!__done){',
    '      /* iframe 带 sandbox（B 站播放器/卡页常见）时 top 导航被禁：',
    '       * 沿 parent 链把请求递给最顶层外壳，由壳执行顶层导航（裸视频页全屏播放） */',
    '      try{var __w=window;while(__w.parent&&__w.parent!==__w){try{__w=__w.parent;}catch(e){break;}}__w.postMessage({__nova:1,type:"nova-p2v",url:PROXY+__p2u},"*");}catch(e){}',
    '    }',
    '  }',
    '}catch(e){}',
    /* 初始 Cookie 快照：同步注入，页面首个 tick 就能读到服务端罐子里的 Cookie。
     * 风控验证码的闭环是"下发 token → 页面写 cookie → 立即 reload → 再读"，
     * 若靠 /__ck 异步回包，reload 后的首次读取会拿到空值，导致验证码反复出现。 */
    'var MYCK_INIT=' + JSON.stringify(cookieHeaderFor(u.hostname)) + ';',
    'var P=window.parent;',
    'function post(m){try{m.__nova=1;P.postMessage(m,"*");}catch(e){}}',
    /* 页面侧行为诊断：postMessage 收发 / cookie 读写上报到 /__log（仅 NOVA_DIAG=1 时服务端记录）。
     * 风控（阿里 x5sec、mtop antiCreep）靠 iframe → 父页面 postMessage 传令牌，
     * 这条通路在浏览器内部，代理日志看不到，必须从页面侧上报。 */
    'var LOGQ=[],LOGT=null;',
    'function nlog(s){try{if(LOGQ.length<120)LOGQ.push(String(s).slice(0,300));if(LOGT)return;LOGT=setTimeout(function(){LOGT=null;if(!LOGQ.length)return;var b=LOGQ.join("\\n");LOGQ=[];try{fetch(PROXY+"/__log?o="+encodeURIComponent(RU)+"&t="+encodeURIComponent(CKT),{method:"POST",body:b,keepalive:true});}catch(e){}},300);}catch(e){}}',
    /* 请求提示头：真实页面地址（供服务端还原 Referer/Origin/sec-fetch-site）+ 本地即时写入的 Cookie。
     * 服务端会消费并剥离这两个头，不会转发给上游站点。 */
    'function novaHints(H){',
    '  try{H.set("x-nova-ref",encodeURIComponent(realHref()));}catch(e){}',
    '  try{var d=ckDirtyH();if(d)H.set("x-nova-ck-set",d);}catch(e){}',
    '  return H;',
    '}',
    /* 原生函数伪装 v2：不在钩子函数上挂 own toString。
     * 原生函数没有 own toString，之前的做法（defineProperty 挂伪装串）会被
     * 反篡改检测识别为"被包装过"，触发页面锁定模式：把 Function.prototype.toString
     * 整个替换成全原生伪装 —— new Function 创建的函数源码全部不可见。
     * 腾讯视频 txv.core.js 的 webpack 内联 Worker 依赖 toString 序列化运行时，
     * 锁定后 blob Worker 语法错误、VShortcut 初始化失败、页头残缺。
     * v2：全局接管 toString + WeakMap 查表，钩子函数表面无痕。 */
    'try{',
    '  var __natMap=new WeakMap();',
    '  var _FTS=Function.prototype.toString;',
    '  var _novaToString=function toString(){try{var s=__natMap.get(this);if(typeof s==="string")return s;}catch(e){}return _FTS.apply(this,arguments);};',
    '  Object.defineProperty(Function.prototype,"toString",{value:_novaToString,writable:true,configurable:true,enumerable:false});',
    '  __natMap.set(_novaToString,"function toString() { [native code] }");',
    '}catch(e){}',
    'function __nat(f,orig){try{',
    '  var s=Function.prototype.toString.call(orig);__natMap.set(f,s);',
    '  var ln=Object.getOwnPropertyDescriptor(orig,"name");if(ln&&typeof ln.value==="string")Object.defineProperty(f,"name",{value:ln.value,configurable:true});',
    '}catch(e){}return f;}',

    /* ---------- 反调试中和 ----------
     * 很多站用 Function("debugger")/eval("debugger")/setInterval 循环做反调试，
     * 开发者工具一旦打开（或打开过）页面就反复暂停（"已在调试程序中暂停"）。
     * 这里在页面脚本运行前把 debugger 语句剥掉：仅当检测到 debugger 时才介入，不影响正常代码。 */
    'try{',
    '  var _NF=window.Function;',
    '  function stripDbg(s){return String(s).replace(/\\bdebugger\\b/g,"");}',
    '  var NF=function Function(){',
    '    var a=[].slice.call(arguments);',
    '    var body=a[a.length-1];',
    '    if(typeof body==="string"&&body.indexOf("debugger")>=0){',
    '      for(var i=0;i<a.length;i++){if(typeof a[i]==="string")a[i]=stripDbg(a[i]);}',
    '    }',
    '    return _NF.apply(this,a);',
    '  };',
    '  try{Object.defineProperty(NF,"length",{value:1,configurable:true});}catch(e){}',
    '  NF.prototype=_NF.prototype;',
    '  NF.prototype.constructor=NF;',
    '  window.Function=__nat(NF,_NF);',
    '  var _EV=window.eval;',
    '  window.eval=__nat(function(s){try{if(typeof s==="string"&&s.indexOf("debugger")>=0)s=stripDbg(s);}catch(e){}return _EV.call(window,s);},_EV);',
    '  var _SI=window.setInterval;',
    '  window.setInterval=__nat(function(f,t){',
    '    try{var s=typeof f==="string"?f:(typeof f==="function"?String(f):"");if(s&&s.indexOf("debugger")>=0)return 0;}catch(e){}',
    '    return _SI.apply(window,arguments);',
    '  },_SI);',
    '}catch(e){}',

    /* ---------- URL 重写 ----------
     * 镜像路径方案：代理 URL = 本站 pathname + 真实 query + ?__nova_url=真实地址。
     * pathname 与真实站点一致（SPA 路由依赖）；真实 query 同时放在可见位置，
     * 页面 JS 读 location.search 才能拿到 q、page 等参数（如淘宝搜索"请输入搜索关键词"问题）。 */
    'function ppath(abs){var u=null;try{u=new URL(abs);}catch(e){}',
    '  if(!u)return "/?__nova_url="+encodeURIComponent(abs);',
    '  try{var q0=u.searchParams.get("__nova_url");if(q0)u=new URL(q0);}catch(e){}',
    '  try{u.searchParams.delete("__nova_url");}catch(e){}',
    '  var s=u.search;',
    '  return u.pathname+s+(s?"&":"?")+"__nova_url="+encodeURIComponent(u.href);}',
    /* 相对地址解析基准用真实地址 realHref()（函数声明提升可用），不能用 document.baseURI：
     * 镜像模式下已不注入 <base>，baseURI 是代理 URL，会把相对链接解析到本站源 */
    'function proxied(u){',
    '  try{',
    '    var s=String(u);',
    '    if(/^(about|javascript|mailto|tel|data|blob|nova):/i.test(s))return s;',
    '    var abs=new URL(s,realHref()).href;',
    '    if(!/^https?:/i.test(abs))return s;',
    '    if(abs.indexOf(PROXY)===0)return s;',
    '    return PROXY+ppath(abs);',
    '  }catch(e){return String(u);}',
    '}',

    /* ---------- Cookie shim：页面内隔离存储，与服务端 Jar 双向同步 ---------- */
    'var myCK={};',
    'try{ckMerge(MYCK_INIT);}catch(e){}',
    'function ckPair(s){var i=String(s).indexOf("=");if(i<=0)return null;return [String(s).slice(0,i).trim(),String(s).slice(i+1).trim()];}',
    'function ckSerialize(){var a=[];for(var k in myCK){if(Object.prototype.hasOwnProperty.call(myCK,k))a.push(k+"="+myCK[k]);}return a.join("; ");}',
    'function ckMerge(t){if(!t)return;t.split(";").forEach(function(p){var pr=ckPair(p);if(pr&&pr[0])myCK[pr[0]]=pr[1];});}',
    'function ckApply(v){',
    '  var parts=String(v).split(";");var p=ckPair(parts[0]);if(!p)return;',
    '  var dead=false;',
    '  for(var i=1;i<parts.length;i++){var s=parts[i].trim();var li=s.indexOf("=");',
    '    var k=(li<0?s:s.slice(0,li)).trim().toLowerCase();var val=li<0?"":s.slice(li+1).trim();',
    '    if(k==="max-age"&&Number(val)<=0)dead=true;',
    '    if(k==="expires"){var d=Date.parse(val);if(!isNaN(d)&&d<Date.now())dead=true;}}',
    '  if(dead){delete myCK[p[0]];}else{myCK[p[0]]=p[1];}',
    '}',
    'var ckQ=[],ckTimer=null;',
    /* 本地刚写入（尚未上报）的 Cookie 原文，按名去重，并共享到 top frame（同源）。
     * 风控闭环是「验证码 iframe 写 cookie → postMessage 通知父页面 → 父页面重试请求」，
     * 写与用发生在两个不同 frame：若各 frame 各存各的，父页面重试就带不上刚写的 x5sec
     * 凭证，表现为"验证通过后立刻又被挑战"（验证码反复出现）。按站点主域分桶，避免串站。
     * 保证"JS 写 Cookie → 立刻发请求"这种反爬 Cookie 能力探测也能通过（真实浏览器是同步可见的）。 */
    'function ckScope(){try{var h=new URL(RU).hostname.split(".");return h.length>2?h.slice(-2).join("."):h.join(".");}catch(e){return String(ORIGIN);}}',
    'function ckStore(){var k=ckScope(),r=null;try{var t=window.top;if(t&&t!==window)r=t;}catch(e){}var o=null;if(r){try{if(!r.__novaCkD)r.__novaCkD={};o=r.__novaCkD;}catch(e){o=null;}}if(!o){if(!window.__novaCkD)window.__novaCkD={};o=window.__novaCkD;}if(!o[k])o[k]={n:0,m:{}};return o[k];}',
    'function ckDirtyH(){try{var s=ckStore(),a=[],now=Date.now();for(var k in s.m){if(!Object.prototype.hasOwnProperty.call(s.m,k))continue;var e=s.m[k];if(!e||now-e.t>10000)continue;if(e.r)a.push(e.r);}return a.length?encodeURIComponent(a.join("\\n")):"";}catch(e){return "";}}',
    'function ckDirtyPush(raw){try{var p=ckPair(raw);if(!p||!p[0])return;var s=ckStore();s.m[p[0]]={r:raw,t:Date.now(),n:++s.n};}catch(e){}}',
    'function ckPost(v){ckQ.push(v);if(ckTimer)return;ckTimer=setTimeout(ckFlush,0);}',
    'function ckFlush(){ckTimer=null;var b=ckQ.join("\\n");ckQ=[];',
    '  try{fetch(PROXY+"/__ck?o="+encodeURIComponent(RU)+"&t="+encodeURIComponent(CKT),{method:"POST",body:b,keepalive:true});}catch(e){}}',
    /* 关键：验证码组件（阿里 x5sec 等）成功后写 Cookie 会立刻 reload 页面，
     * 批量定时器被打断会导致验证通过的 Cookie 永远不上报、验证码反复出现。
     * 故上报改为下一 tick 即刻冲刷，且页面卸载/隐藏时同步冲刷（fetch keepalive 保证卸载后仍能送达）。 */
    'function ckFlushNow(){if(ckTimer){clearTimeout(ckTimer);ckTimer=null;ckFlush();}}',
    'try{',
    '  window.addEventListener("pagehide",ckFlushNow,true);',
    '  window.addEventListener("beforeunload",ckFlushNow,true);',
    '  document.addEventListener("visibilitychange",function(){if(document.visibilityState==="hidden")ckFlushNow();},true);',
    '}catch(e){}',
    'var ckLast=0,ckPend=false;',
    'function ckSync(){',
    '  var now=Date.now();',
    '  if(now-ckLast<2000){if(!ckPend){ckPend=true;setTimeout(function(){ckPend=false;ckSync();},2100);}return;}',
    '  ckLast=now;',
    '  try{fetch(PROXY+"/__ck?o="+encodeURIComponent(RU)+"&t="+encodeURIComponent(CKT)).then(function(r){return r.text();}).then(ckMerge);}catch(e){}}',
    'try{fetch(PROXY+"/__ck?o="+encodeURIComponent(RU)+"&t="+encodeURIComponent(CKT)).then(function(r){return r.text();}).then(ckMerge);}catch(e){}',
    'try{',
    '  var dcp=Object.getOwnPropertyDescriptor(Document.prototype,"cookie");',
    '  Object.defineProperty(document,"cookie",{configurable:true,',
    '    get:function(){var s=ckSerialize();try{if(/x5sec|_m_h5_smt|smToken/.test(s))nlog("CK_R "+s.slice(0,240));}catch(e){}return s;},',
    '    set:function(v){try{nlog("CK_W "+String(v).slice(0,240));}catch(e){}ckApply(v);ckDirtyPush(v);ckPost(v);}});',
    '}catch(e){}',

    /* ---------- 跨框架通信观测（只记录，不改行为） ---------- */
    'try{',
    '  var _pm=window.postMessage;',
'  var _ph=null,_rh=null;try{_ph=String(location.host);_rh=new URL(RU).host;}catch(e){}',
  /* 风控令牌会把 window.location.host 内嵌进载荷；代理下它是 127.0.0.1:7180，
   * 服务端校验必然不认。发出前把该字段还原成真实站点 host。 */
'  function fixPm(m){try{',
'    if(typeof m!=="string"||!_ph||!_rh||m.indexOf(_ph)<0)return m;',
'    var Q=String.fromCharCode(34),BS=String.fromCharCode(92);',
'    var eA=BS+Q+"host"+BS+Q+":"+BS+Q+_ph+BS+Q,eB=BS+Q+"host"+BS+Q+":"+BS+Q+_rh+BS+Q;',
'    var rA=Q+"host"+Q+":"+Q+_ph+Q,rB=Q+"host"+Q+":"+Q+_rh+Q;',
'    return m.split(eA).join(eB).split(rA).join(rB);',
'  }catch(e){return m;}}',
'  window.postMessage=__nat(function(m,t){try{ckFlushNow();}catch(e){}try{var tg="";try{tg=(t&&t.origin)||String(t);}catch(e){}nlog("PM_OUT to="+tg+" d="+String(typeof m==="string"?m:(m&&m.type)||Object.prototype.toString.call(m)).slice(0,240));}catch(e){}try{var ar=[].slice.call(arguments);if(ar.length)ar[0]=fixPm(ar[0]);return _pm.apply(window,ar);}catch(e){}return _pm.apply(window,arguments);},_pm);',
    '}catch(e){}',
    'try{',
    '  var _wa=window.addEventListener;',
    '  window.addEventListener=__nat(function(t,f,o){',
    '    if(String(t)==="message"&&typeof f==="function"){',
    '      var g=function(ev){try{nlog("PM_IN origin="+String(ev&&ev.origin)+" from="+(ev&&ev.source===window.parent?"parent":(ev&&ev.source===window?"self":"other"))+" d="+String(ev&&ev.data).slice(0,240));}catch(e){}return f.apply(this,arguments);};',
    '      return _wa.call(window,t,g,o);',
    '    }',
    '    return _wa.apply(window,arguments);',
    '  },_wa);',
    '}catch(e){}',
    'try{nlog("LOAD "+RU+" selfIsTop="+(window.self===window.top)+" parentIsSelf="+(P===window)+" frames="+window.frames.length);}catch(e){}',
    /* JS 异常上报：页面脚本崩溃是"加载不全"类问题的主因，capture 阶段连资源错误一起抓 */
    'try{window.addEventListener("error",function(e){try{nlog("JSERR "+(e&&e.message||e&&e.target&&e.target.tagName||"unknown")+" @ "+String((e&&e.filename)||(e&&e.target&&e.target.src)||"").slice(-90)+":"+(e&&e.lineno||0)+":"+(e&&e.colno||0));}catch(x){}},true);}catch(e){}',
    'try{window.addEventListener("unhandledrejection",function(e){try{var r=e&&e.reason;var s="";try{s=(r&&(r.stack||r.message))||String(r);}catch(x){}nlog("JSREJ "+String(s).slice(0,300));}catch(x){}});}catch(e){}',

    /* ---------- 存储隔离 ---------- */
    'try{',
    '  var px="__nova@"+ORIGIN+"@";',
    '  var real=window.localStorage;',
    '  function mkKeys(){var a=[];for(var i=0;i<real.length;i++){var k=real.key(i);if(k&&k.indexOf(px)===0)a.push(k);}return a;}',
    '  var LS={getItem:function(k){return real.getItem(px+k);},setItem:function(k,v){return real.setItem(px+k,String(v));},',
    '    removeItem:function(k){return real.removeItem(px+k);},clear:function(){var a=mkKeys();for(var i=0;i<a.length;i++)real.removeItem(a[i]);},',
    '    key:function(i){var a=mkKeys();return i<a.length?a[i].slice(px.length):null;}};',
    '  try{Object.defineProperty(LS,"length",{get:function(){return mkKeys().length;}});}catch(e){}',
    '  try{Object.defineProperty(window,"localStorage",{configurable:true,get:function(){return LS;}});}catch(e){}',
    '  var mem={};',
    '  var SS={getItem:function(k){return Object.prototype.hasOwnProperty.call(mem,k)?mem[k]:null;},setItem:function(k,v){mem[k]=String(v);},',
    '    removeItem:function(k){delete mem[k];},clear:function(){mem={};},key:function(i){var a=Object.keys(mem);return i<a.length?a[i]:null;}};',
    '  try{Object.defineProperty(SS,"length",{get:function(){return Object.keys(mem).length;}});}catch(e){}',
    '  try{Object.defineProperty(window,"sessionStorage",{configurable:true,get:function(){return SS;}});}catch(e){}',
    '}catch(e){}',

    /* ---------- fetch 接管 ---------- */
    'function patchResp(p,realUrl){',
    '  if(!p||!p.then)return p;',
    '  return p.then(function(res){',
    '    try{if(res&&realUrl)Object.defineProperty(res,"url",{value:realUrl,configurable:true});}catch(e){}',
    '    try{var h=res&&res.headers&&res.headers.get("x-nova-ck");if(h)ckMerge(decodeURIComponent(h));}catch(e){}',
    '    ckSync();return res;',
    '  });',
    '}',
    'try{',
    '  var _fetch=window.fetch;',
    '  if(_fetch){',
    '    window.fetch=__nat(function(input,init){',
    '      try{',
    '        if(input&&typeof input==="object"&&typeof input.url==="string"){',
    '          var ru=input.url;var nu=proxied(ru);',
    '          if(nu!==ru){',
    '            var req=null;',
    '            try{req=new Request(nu,input);}catch(e){}',
    '            if(req)return patchResp(_fetch.call(window,req,init),ru);',
    '            init=init||{};init.method=input.method;init.headers=input.headers;',
    '            return patchResp(_fetch.call(window,nu,init),ru);',
    '          }',
    '          return patchResp(_fetch.call(window,input,init),ru);',
    '        }',
    '        var su=String(input);var nu2=proxied(su);',
    '        init=init||{};',
    '        try{init.headers=novaHints(new Headers(init.headers||{}));}catch(e){}',
    '        return patchResp(_fetch.call(window,nu2,init),nu2===su?null:su);',
    '      }catch(e){return _fetch.apply(window,arguments);}',
    '    },_fetch);',
    '  }',
    '}catch(e){}',

    /* ---------- XMLHttpRequest 接管 ---------- */
    'try{',
    '  var X=window.XMLHttpRequest&&window.XMLHttpRequest.prototype;',
    '  if(X){',
    '    var _open=X.open,_send=X.send;',
    '    X.open=__nat(function(m,u){',
    '      this.__nOrig=String(u);this.__nReal=proxied(u);',
    '      return _open.apply(this,[m,this.__nReal].concat([].slice.call(arguments,2)));',
    '    },_open);',
    '    X.send=__nat(function(){',
    '      var x=this;',
    '      try{x.setRequestHeader("x-nova-ref",encodeURIComponent(realHref()));}catch(e){}',
    '      try{var d=ckDirtyH();if(d)x.setRequestHeader("x-nova-ck-set",d);}catch(e){}',
    '      if(x.__nOrig){try{Object.defineProperty(x,"responseURL",{get:function(){return x.__nOrig;},configurable:true});}catch(e){}}',
    '      x.addEventListener("readystatechange",function(){try{if(x.readyState>=2){var h=x.getResponseHeader("x-nova-ck");if(h)ckMerge(decodeURIComponent(h));}}catch(e){}});',
    '      x.addEventListener("loadend",function(){ckSync();});',
    '      return _send.apply(x,arguments);',
    '    },_send);',
    '  }',
    '}catch(e){}',

    /* ---------- sendBeacon / EventSource / WebSocket / SW ---------- */
    'try{if(navigator.sendBeacon){var _sb=navigator.sendBeacon.bind(navigator);navigator.sendBeacon=__nat(function(u,d){try{return _sb(proxied(String(u)),d);}catch(e){return false;}},navigator.sendBeacon);}}catch(e){}',
    'try{var _ES=window.EventSource;if(_ES){window.EventSource=function(u,c){return new _ES(proxied(String(u)),c);};window.EventSource.prototype=_ES.prototype;}}catch(e){}',
    'try{',
    '  var _WS=window.WebSocket;',
    '  if(_WS){',
    '    window.WebSocket=function(u,p){',
    '      var uu=String(u);',
    '      try{var abs=new URL(uu,document.baseURI).href;',
    '        if(/^http:/i.test(abs))abs="ws:"+abs.slice(5);',
    '        else if(/^https:/i.test(abs))abs="wss:"+abs.slice(6);',
    '        if(/^(ws|wss):/i.test(abs))uu=abs;',
    '      }catch(e){}',
    '      return p===undefined?new _WS(uu):new _WS(uu,p);',
    '    };',
    '    window.WebSocket.prototype=_WS.prototype;',
    '    ["CONNECTING","OPEN","CLOSING","CLOSED"].forEach(function(k){try{window.WebSocket[k]=_WS[k];}catch(e){}});',
    '  }',
    '}catch(e){}',
    'try{if(navigator.serviceWorker&&navigator.serviceWorker.register){navigator.serviceWorker.register=function(){return Promise.reject(new Error("disabled in nova proxy"));};}}catch(e){}',

    /* ---------- createElement 接管：动态 <script> 创建时改写 src ----------
     * script 元素插入 DOM 即同步开始抓取（already started 标志），MutationObserver
     * 微任务必然输掉竞态。必须在创建时给元素装改写版 src setter（JSONP 验证码 SDK
     * 的标准姿势是先设 src 再 append，天然无竞态）。getter 回传原始 URL。 */
    'try{',
    '  var _ce=document.createElement.bind(document);',
    '  var _scSrc=Object.getOwnPropertyDescriptor(HTMLScriptElement.prototype,"src");',
    '  document.createElement=__nat(function(tag){',
    '    var el=_ce.apply(document,arguments);',
    '    try{',
    '      if(el&&el.tagName==="SCRIPT"&&_scSrc){',
    '        var _fix=function(v){',
    '          try{',
    '            var sv=String(v);',
    '            if(!/^(about|javascript|data|blob|nova):/i.test(sv)){',
    '              var a2=new URL(sv,realHref()).href;',
    '              if(/^https?:/i.test(a2)&&a2.indexOf(PROXY)!==0){',
    '                var p2=PROXY+ppath(a2);',
    '                p2+=String.fromCharCode(38)+"__nova_ref="+encodeURIComponent(realHref());',
    '                return p2;',
    '              }',
    '            }',
    '          }catch(e){}',
    '          return v;',
    '        };',
    '        Object.defineProperty(el,"src",{',
    '          set:function(v){try{el.__nOrig=v;}catch(e){}return _scSrc.set.call(this,_fix(v));},',
    '          get:function(){try{if(el.__nOrig)return el.__nOrig;}catch(e){}return _scSrc.get.call(this);},',
    '          configurable:true,enumerable:true',
    '        });',
    '      }',
    '    }catch(e){}',
    '    return el;',
    '  },document.createElement);',
    '}catch(e){}',

    /* ---------- 动态媒体/样式资源 URL 归一：绝对地址改走代理 ----------
     * 页面 JS 常用 JSON 数据里的绝对地址直接 img.src=... / video.src=...，
     * 不改写就直连真实网络：跨域模块脚本、字体等被 CDN 的 CORS 白名单拒绝。
     * img/video/audio/source/link/track/embed 的 src|href 属性 setter 与
     * setAttribute 统一接管；getter 回传原始值，页面逻辑不受影响。 */
    /* blob 诊断：页面常把 XHR 拉到的文本包成 blob 再当脚本执行，
     * 内容错了只会报 blob:xxx SyntaxError，看不到真实内容 —— 这里采样记下前 150 字符 */
    'try{',
    '  var _cou=URL.createObjectURL.bind(URL);',
    '  var _blobN=0;',
    '  URL.createObjectURL=function(obj){',
    '    try{',
    '      if(_blobN<5&&obj&&typeof Blob!=="undefined"&&obj instanceof Blob){',
    '        _blobN++;',
    '        obj.text().then(function(t){nlog("BLOB type="+obj.type+" size="+obj.size+" head="+String(t).slice(0,150).replace(/\\s+/g," "));}).catch(function(){});',
    '      }',
    '    }catch(e){}',
    '    return _cou(obj);',
    '  };',
    '}catch(e){}',
    'function __nFixU(v){',
    '  try{',
    '    var sv=String(v);',
    '    if(/^(about|javascript|data|blob|nova):/i.test(sv))return v;',
    '    if(sv.charAt(0)==="/"&&sv.charAt(1)!=="/")return v;',
    '    var a2=new URL(sv,realHref()).href;',
    '    if(/^https?:/i.test(a2)&&a2.indexOf(PROXY)!==0){',
    '      var p2=PROXY+ppath(a2);',
    '      try{p2+=String.fromCharCode(38)+"__nova_ref="+encodeURIComponent(realHref());}catch(e){}',
    '      return p2;',
    '    }',
    '  }catch(e){}',
    '  return v;',
    '}',
    'try{',
    '  [[window.HTMLImageElement,"src"],[window.HTMLMediaElement,"src"],[window.HTMLSourceElement,"src"],',
    '   [window.HTMLLinkElement,"href"],[window.HTMLTrackElement,"src"],[window.HTMLEmbedElement,"src"]',
    '  ].forEach(function(pr){',
    '    var C=pr[0],N=pr[1];if(!C)return;',
    '    var d=Object.getOwnPropertyDescriptor(C.prototype,N);if(!d||!d.set)return;',
    '    Object.defineProperty(C.prototype,N,{configurable:true,enumerable:d.enumerable,',
    '      set:function(v){try{this.__nOrig=v;}catch(e){}return d.set.call(this,__nFixU(v));},',
    '      get:function(){try{if(this.__nOrig)return this.__nOrig;}catch(e){}return d.get.call(this);}});',
    '  });',
    '}catch(e){}',
    'try{',
    '  var _sa=Element.prototype.setAttribute;',
    '  Element.prototype.setAttribute=__nat(function(n,v){',
    '    try{',
    '      var ln=String(n).toLowerCase();',
    '      if(ln==="src"||ln==="poster"||ln==="href"){',
    '        var tg=this.tagName||"";',
    '        var ok=(ln==="href")?(tg==="LINK"):(tg!=="A"&&tg!=="AREA"&&tg!=="BASE"&&tg!=="IFRAME"&&tg!=="SCRIPT");',
    '        if(ok){var nv=__nFixU(v);if(nv!==v){var ar=[].slice.call(arguments);ar[1]=nv;return _sa.apply(this,ar);}}',
    '      }',
    '    }catch(e){}',
    '    return _sa.apply(this,arguments);',
    '  },_sa);',
    '}catch(e){}',

    /* ---------- 动态 iframe / script 观察器兜底（innerHTML 等不经 createElement 的路径） ----------
     * 动态 <script src>（JSONP、验证码 SDK 如网易易盾）若直连，Referer 是 127.0.0.1，
     * 会被 captchaId 域名绑定校验拒绝（滑块显示"正在加载，请稍后重试"）。
     * 与 iframe 一并改写走代理，由服务端把 Referer/Origin 还原成真实页面地址。 */
    'function fixFrame(el){',
    '  try{',
    '    if(!el)return;',
    '    var tg=el.tagName;',
    '    var isMedia=(tg==="IMG"||tg==="VIDEO"||tg==="AUDIO"||tg==="SOURCE"||tg==="TRACK"||tg==="EMBED"||tg==="LINK");',
    '    if(tg!=="IFRAME"&&tg!=="SCRIPT"&&!isMedia)return;',
    '    if(tg==="SCRIPT"){var tp=(el.getAttribute("type")||"").toLowerCase();if(tp&&tp!=="text/javascript"&&tp!=="application/javascript")return;}',
    '    if(tg==="LINK"){var rl=(el.getAttribute("rel")||"").toLowerCase();if(/preconnect|dns-prefetch/.test(rl))return;}',
    '    var at=isMedia&&tg==="LINK"?"href":"src";',
    '    var s=el.getAttribute(at);',
    '    if(!s)return;',
    '    if(/^(about|javascript|data|blob):/i.test(s))return;',
    '    var abs=new URL(s,realHref()).href;',
    '    if(!/^https?:/i.test(abs))return;',
    '    if(abs.indexOf(PROXY)===0)return;',
    '    var p=PROXY+ppath(abs);',
    '    try{p+=String.fromCharCode(38)+"__nova_ref="+encodeURIComponent(realHref());}catch(e){}',
    '    if(el.getAttribute(at)!==p)el.setAttribute(at,p);',
    '  }catch(e){}',
    '}',
    'try{',
    '  var mo=new MutationObserver(function(ms){',
    '    for(var i=0;i<ms.length;i++){',
    '      var m=ms[i];',
    '      if(m.type==="attributes"){fixFrame(m.target);}',
    '      else if(m.addedNodes){',
    '        for(var j=0;j<m.addedNodes.length;j++){',
    '          var n=m.addedNodes[j];',
    '          if(n&&n.nodeType===1){',
    '            if(n.tagName==="IFRAME"||n.tagName==="SCRIPT"||n.tagName==="IMG"||n.tagName==="VIDEO"||n.tagName==="AUDIO"||n.tagName==="SOURCE"||n.tagName==="LINK"||n.tagName==="TRACK"||n.tagName==="EMBED")fixFrame(n);',
    '            if(n.querySelectorAll){var l=n.querySelectorAll("iframe[src],script[src],img[src],video[src],audio[src],source[src],link[href],track[src],embed[src]");for(var k2=0;k2<l.length;k2++)fixFrame(l[k2]);}',
    '          }',
    '        }',
    '      }',
    '    }',
    '  });',
    '  mo.observe(document.documentElement||document,{childList:true,subtree:true,attributes:true,attributeFilter:["src","href","poster"]});',
    '}catch(e){}',

    /* ---------- 导航劫持 ---------- */
    /* ---------- 媒体嗅探补充：video/audio 元素实际播放的地址 ----------
     * 服务端按 Content-Type/扩展名嗅探已覆盖绝大多数场景；
     * 这里捕获 <video>/<audio> 的 loadstart，把内容类型非典型的媒体也报给外壳。 */
    'function novaRepMedia(el){try{var u=(el.currentSrc||el.src||"")+"";if(/^https?:/i.test(u))post({type:"media",url:u});}catch(e){}}',
    'document.addEventListener("loadstart",function(e){var t=e.target||null;if(!t||t.nodeType!==1)return;var m=(t.tagName==="VIDEO"||t.tagName==="AUDIO")?t:(t.tagName==="SOURCE"?t.parentElement:null);if(m)novaRepMedia(m);},true);',

    'function abs(u){try{return new URL(u,realHref()).href;}catch(e){return String(u);}}',
    'function findA(n){while(n&&n.nodeType===1&&n.tagName!=="A")n=n.parentElement;return n&&n.tagName==="A"?n:null;}',
    /* 下载类链接（download 属性 / 常见文件扩展名）改道 Nova 下载管理器：
     * iframe 内原生下载会落到宿主浏览器的下载目录、绕过 Nova 的 Cookie/Referer 体系，
     * 且无进度可见。blob/data 地址无法在服务端复取，仍交给浏览器。 */
    'var DL_RE=/\\.(zip|rar|7z|tar|gz|tgz|bz2|xz|exe|msi|dmg|pkg|deb|rpm|apk|ipa|iso|img|cab|pdf|docx?|xlsx?|pptx?|csv|epub|mobi|azw3|ttf|otf|woff2?|jar|crx)([?#]|$)/i;',
    /* 用 window 捕获 + stopImmediatePropagation：百度/必应等站点在 document 上也挂了
     * 点击处理器（会额外调用 window.open 造成重复开标签），stopPropagation 挡不住
     * 同节点上的其他监听器，必须用 stopImmediatePropagation 才能完全接管一次点击。 */
    'window.addEventListener("click",function(e){',
    '  var a=findA(e.target);if(!a)return;',
    '  var raw=a.getAttribute("href");',
    '  if(!raw||raw.charAt(0)==="#")return;',
    '  if(/^(javascript|mailto|tel|data|blob|about):/i.test(raw))return;',
    '  var hrefAbs=abs(raw);',
    '  if(a.hasAttribute("download")||DL_RE.test(hrefAbs)){',
    '    if(/^(blob|data):/i.test(hrefAbs))return;',
    '    e.preventDefault();e.stopImmediatePropagation();',
    '    post({type:"download",url:hrefAbs,name:(a.getAttribute("download")||""),ref:realHref()});',
    '    return;',
    '  }',
    '  e.preventDefault();e.stopImmediatePropagation();',
    '  post({type:"navigate",url:hrefAbs,newTab:(a.target==="_blank"||e.ctrlKey||e.metaKey||e.shiftKey)});',
    '},true);',
    'document.addEventListener("auxclick",function(e){',
    '  if(e.button!==1)return;var a=findA(e.target);if(!a)return;var raw=a.getAttribute("href");if(!raw)return;',
    '  e.preventDefault();post({type:"navigate",url:abs(raw),newTab:true});',
    '},true);',
    'document.addEventListener("submit",function(e){',
    '  var f=e.target;if(!f||f.tagName!=="FORM")return;',
    '  var action=abs(f.getAttribute("action")||location.href);',
    '  var method=(f.getAttribute("method")||"get").toLowerCase();',
    '  try{',
    '    var fd=new FormData(f),pairs=[];',
    '    fd.forEach(function(v,k){if(typeof v==="string")pairs.push([k,v]);});',
    '    e.preventDefault();',
    '    if(method==="post"){post({type:"form",action:action,pairs:pairs});}',
    '    else{',
    '      var qs=pairs.map(function(p){return encodeURIComponent(p[0])+"="+encodeURIComponent(p[1]);}).join("&");',
    '      post({type:"navigate",url:action+(action.indexOf("?")>=0?"&":"?")+qs});',
    '    }',
    '  }catch(err){}',
    '},true);',
    'window.open=__nat(function(u){if(u)post({type:"navigate",url:abs(String(u)),newTab:true});return null;},window.open);',
    /* location.assign / replace 改道镜像 URL（SPA 常用跳转方式） */
    'try{',
    '  location.assign=function(u){location.href=proxied(u);};',
    '  location.replace=function(u){location.href=proxied(u);};',
    '}catch(e){}',

    /* ---------- history 钩子：SPA 路由切换时同步外壳地址与标题 ----------
     * 关键：SPA 路由器（vue-router/react-router/Next.js）会调用
     * pushState/replaceState 写入真实站点 URL（如 https://juejin.cn/post/1），
     * 而代理文档的源是本站，浏览器会抛 SecurityError 导致路由器崩溃、
     * 点击链接全部失效。必须在调用原始方法前把 URL 重写为镜像代理 URL。
     * 注意：有些站点（如 B 站）直接传 location.href（即代理 URL 本身），
     * 若不先解包会套娃成双重镜像，导致 Referer 还原失败、API 被风控拦截。 */
    'function unproxy(u){var g=0;u=String(u);while(g++<5&&u.indexOf(PROXY)===0){var m=/[?&]__nova_url=([^&]+)/.exec(u);if(!m)break;try{u=decodeURIComponent(m[1]);}catch(e){break;}}return u;}',
    'function realHref(){try{var m=/[?&]__nova_url=([^&]+)/.exec(location.search);if(m)return unproxy(decodeURIComponent(m[1]))+location.hash;}catch(e){}return location.href;}',
    'function stateUrl(u){try{if(u==null||u==="")return null;var abs=new URL(String(u),realHref());return PROXY+ppath(new URL(unproxy(abs.href)));}catch(e){return null;}}',
    'try{',
    '  var _ps=history.pushState,_rs=history.replaceState;',
    '  history.pushState=__nat(function(s,t,u){var nu=stateUrl(u);var r=(nu===null)?_ps.apply(this,arguments):_ps.call(this,s,t,nu);post({type:"meta",title:document.title||"",url:realHref()});return r;},_ps);',
    '  history.replaceState=__nat(function(s,t,u){var nu=stateUrl(u);var r=(nu===null)?_rs.apply(this,arguments):_rs.call(this,s,t,nu);post({type:"meta",title:document.title||"",url:realHref()});return r;},_rs);',
    '}catch(e){}',

    /* ---------- 状态上报 ---------- */
    'function report(){post({type:"meta",title:document.title||"",url:realHref()});}',
    'if(document.readyState==="loading")document.addEventListener("DOMContentLoaded",report);else report();',
    'window.addEventListener("load",report);window.addEventListener("hashchange",report);',
    'setTimeout(report,800);setTimeout(report,2500);setTimeout(report,6000);',
    'document.addEventListener("keydown",function(e){',
    '  if(!(e.ctrlKey||e.metaKey))return;',
    '  post({type:"key",key:(e.key||"").toLowerCase(),ctrl:e.ctrlKey,meta:e.metaKey,shift:e.shiftKey,alt:e.altKey});',
    '},true);',
    '})();<' + '/script>',
  ].join('\n');
}

/* ------------------------------------------------------------------ *
 * HTML 重写
 * ------------------------------------------------------------------ */
function decodeBody(pres) {
  const enc = String(pres.headers['content-encoding'] || '').toLowerCase();
  if (enc.includes('br')) return pres.pipe(zlib.createBrotliDecompress());
  if (enc.includes('gzip')) return pres.pipe(zlib.createGunzip());
  if (enc.includes('deflate')) return pres.pipe(zlib.createUnzip());
  return pres;
}

function detectCharset(buf, contentType) {
  let m = /charset\s*=\s*["']?([\w-]+)/i.exec(contentType || '');
  if (m) return m[1].toLowerCase();
  const head = buf.slice(0, 8192).toString('latin1');
  m = /<meta[^>]+charset\s*=\s*["']?([\w-]+)/i.exec(head);
  if (m) return m[1].toLowerCase();
  return 'utf-8';
}

function decodeText(buf, charset) {
  const cs = String(charset || 'utf-8').toLowerCase();
  if (cs === 'utf-8' || cs === 'utf8') return buf.toString('utf8');
  try {
    return new TextDecoder(cs, { fatal: false }).decode(buf);
  } catch (e) {
    try {
      return new TextDecoder('utf-8', { fatal: false }).decode(buf);
    } catch (e2) {
      return buf.toString('utf8');
    }
  }
}

/* 镜像路径代理 URL：pathname 与真实站点一致（SPA 路由依赖），
 * 真实 query 放可见位置（页面 JS 读 location.search 依赖），完整真实地址放 __nova_url 参数 */
function proxyUrlFor(realUrl) {
  let u;
  try { u = new URL(realUrl); } catch (e) { return '/?__nova_url=' + encodeURIComponent(realUrl); }
  /* 输入若已带 __nova_url（页面 JS 把我们改写过的地址再次按真实源解析后传回），
   * 内层参数才是真实地址，以外层主机为准会 404（如腾讯视频 page-slice 组件） */
  try {
    const q = u.searchParams.get('__nova_url');
    if (q) u = new URL(q);
  } catch (e) { /* ignore */ }
  try { u.searchParams.delete('__nova_url'); } catch (e) { /* ignore */ }
  const s = u.search;
  return u.pathname + s + (s ? '&' : '?') + '__nova_url=' + encodeURIComponent(u.href);
}

function rewriteIframeSrcs(html, realUrl) {
  return html.replace(
    /<iframe\b([^>]*?)\bsrc\s*=\s*(["'])([^"']+)\2/gi,
    (m, pre, q, src) => {
      const t = attrUrlDecode(src.trim());
      if (!/^https?:/i.test(t) && !/^\//.test(t) && !/^\./.test(t)) return m;
      if (t.startsWith('/__p?') || t.includes('__nova_url=')) return m;
      let abs;
      try {
        abs = new URL(t, realUrl).href;
      } catch (e) {
        return m;
      }
      return '<iframe' + pre + ' src=' + q + proxyUrlFor(abs) + q;
    }
  );
}

function rewriteMetaRefresh(html, realUrl) {
  return html.replace(
    /(<meta[^>]+http-equiv\s*=\s*["']?refresh["']?[^>]*content\s*=\s*["'])([^"']*)(["'])/gi,
    (m, pre, content, post) => {
      const mm = /url\s*=\s*(.+)$/i.exec(content);
      if (!mm) return m;
      const raw = mm[1].trim().replace(/^["']|["']$/g, '');
      try {
        const abs = new URL(raw, realUrl).href;
        return pre + content.replace(mm[1], proxyUrlFor(abs)) + post;
      } catch (e) {
        return m;
      }
    }
  );
}

/* ------------------------------------------------------------------ *
 * 子资源 URL 改写（script/link/img/媒体/内联样式）
 * 页面 HTML 里的绝对地址与协议相对地址（//host/...）若不改写会直连真实
 * 网络，绕过代理：跨域模块脚本/字体被 CDN 的 CORS 白名单拒绝（Origin 是
 * 代理源而非站点源），表现为整页只渲染骨架屏。统一改写为镜像路径 +
 * __nova_url，由代理转发并附加 access-control-allow-origin: *。
 * 只处理标签属性，不触碰 <script> 内联代码与 JSON 文本。
 * ------------------------------------------------------------------ */
const ABS_URL_RE = /^(?:\/\/|https?:\/\/)/i;

/* 从 HTML 原文正则提取的属性值未做实体解码（浏览器解析属性时才会解码），
 * 百度等站点属性里写 ...u=1,2&amp;fm=217 —— 不解码就改写，上游会收到
 * 含 "&amp;" 字面量的 URL 直接 400。这里还原最常见的数值/命名实体。 */
function attrUrlDecode(u) {
  return u
    .replace(/&amp;/gi, '&')
    .replace(/&#0*38;|&#[xX]0*26;/g, '&');
}

function rewriteSrcset(v, base) {
  return v
    .split(',')
    .map((part) => {
      const t = part.trim();
      if (!t) return part;
      const m = /^(\S+)(?:\s+(.*))?$/.exec(t);
      if (!m || !ABS_URL_RE.test(m[1])) return t;
      const raw = attrUrlDecode(m[1]);
      const p = proxyUrlFor(raw.charAt(0) === '/' ? new URL(raw, base).href : raw);
      return p + (m[2] ? ' ' + m[2] : '');
    })
    .join(', ');
}

function rewriteCssUrls(css, base) {
  return css.replace(/url\(\s*(['"]?)([^'")]+)\1\s*\)/gi, (m, q, u) => {
    const url = attrUrlDecode(u.trim());
    if (!ABS_URL_RE.test(url)) return m;
    try {
      const abs = url.charAt(0) === '/' ? new URL(url, base).href : url;
      const p = proxyUrlFor(abs);
      return p ? 'url(' + q + p + q + ')' : m;
    } catch (e) {
      return m;
    }
  });
}

function rewriteSubresources(html, base) {
  /* <script src> */
  html = html.replace(
    /(<script\b[^>]*?\bsrc\s*=\s*)(["'])([^"']+)\2/gi,
    (m, pre, q, u) => {
      if (!ABS_URL_RE.test(u)) return m;
      try {
        const abs = attrUrlDecode(u).charAt(0) === '/' ? new URL(attrUrlDecode(u), base).href : attrUrlDecode(u);
        return pre + q + proxyUrlFor(abs) + q;
      } catch (e) {
        return m;
      }
    }
  );
  /* <link href>（跳过预连接提示类，改写无意义反而多占一条代理连接） */
  html = html.replace(/<link\b[^>]*>/gi, (tag) => {
    if (/rel\s*=\s*["'][^"']*(?:preconnect|dns-prefetch)/i.test(tag)) return tag;
    return tag.replace(/\bhref\s*=\s*(["'])([^"']+)\1/i, (m, q, u) => {
      if (!ABS_URL_RE.test(u)) return m;
      try {
        const abs = attrUrlDecode(u).charAt(0) === '/' ? new URL(attrUrlDecode(u), base).href : attrUrlDecode(u);
        return 'href=' + q + proxyUrlFor(abs) + q;
      } catch (e) {
        return m;
      }
    });
  });
  /* 常见媒体/图片标签：标签内所有 src/poster/srcset/data-src/data-original 统一改写
   * （相对地址由镜像路径天然覆盖，不动） */
  html = html.replace(
    /<(img|source|video|audio|track|input|embed)\b([^>]*)>/gi,
    (m, tag, attrs) => {
      let na = attrs.replace(
        /(\b(?:src|poster|data-src|data-original)\s*=\s*)(["'])([^"']+)\2/gi,
        (mm, pre, q, u) => {
          if (!ABS_URL_RE.test(u)) return mm;
          try {
            const abs = attrUrlDecode(u).charAt(0) === '/' ? new URL(attrUrlDecode(u), base).href : attrUrlDecode(u);
            return pre + q + proxyUrlFor(abs) + q;
          } catch (e) {
            return mm;
          }
        }
      );
      na = na.replace(/(\bsrcset\s*=\s*)(["'])([^"']+)\2/gi, (mm, pre, q, v) => {
        const r = rewriteSrcset(v, base);
        return r !== v ? pre + q + r + q : mm;
      });
      return '<' + tag + na + '>';
    }
  );
  /* 内联 <style> 块与 style 属性里的 url() */
  html = html.replace(/(<style\b[^>]*>)([\s\S]*?)(<\/style>)/gi, (m, o, body, cl) => {
    const r = rewriteCssUrls(body, base);
    return r !== body ? o + r + cl : m;
  });
  html = html.replace(
    /(\sstyle\s*=\s*)(["'])((?:(?!\2).)*url\((?:(?!\2).)*)\2/gi,
    (m, pre, q, css) => {
      const r = rewriteCssUrls(css, base);
      return r !== css ? pre + q + r + q : m;
    }
  );
  return html;
}

/* m3u8 播放列表改写：页面内 hls.js 直接加载的 m3u8，其内容里的分片/子列表/
 * KEY URI 若不改写，hls.js 会以 m3u8 的代理 URL 为 base 解析相对路径，
 * 丢掉 __nova_url 参数 → 分片 404（第三方影视站播放黑屏的主因）。 */
function rewriteM3u8(text, baseUrl) {
  return text
    .split('\n')
    .map((line) => {
      const t = line.trim();
      if (!t) return line;
      if (t.charAt(0) === '#') {
        /* 属性列表行里的 URI="..."（KEY/MAP/MEDIA/I-FRAME-STREAM-INF 等） */
        if (t.includes('URI="')) {
          return line.replace(/URI="(.*?)"/gi, (m, uri) => {
            if (!uri || uri.includes('__nova_url=')) return m;
            try {
              const abs = new URL(attrUrlDecode(uri), baseUrl).href;
              return 'URI="' + proxyUrlFor(abs) + '"';
            } catch (e) {
              return m;
            }
          });
        }
        return line;
      }
      if (t.includes('__nova_url=')) return line;
      try {
        const abs = new URL(attrUrlDecode(t), baseUrl).href;
        return proxyUrlFor(abs);
      } catch (e) {
        return line;
      }
    })
    .join('\n');
}

function rewriteHtml(html, realUrl) {  // 1) 干掉页面内的 CSP / content-type meta
  html = html.replace(
    /<meta[^>]+http-equiv\s*=\s*["']?content-security-policy["']?[^>]*>/gi,
    ''
  );
  html = html.replace(/<meta[^>]+http-equiv\s*=\s*["']?content-type["']?[^>]*>/gi, '');
  // 2) 统一字符集声明为 utf-8（已按原编码解码并重新以 utf-8 输出）
  html = html.replace(/<meta[^>]+charset\s*=\s*["']?[\w-]+["']?[^>]*>/gi, '');
  // 3) 去掉 SRI
  html = html.replace(/\sintegrity\s*=\s*["'][^"']*["']/gi, '');
  // 4) 静态 iframe / meta refresh 重写
  html = rewriteIframeSrcs(html, realUrl);
  html = rewriteMetaRefresh(html, realUrl);
  // 5) 子资源（script/link/img/媒体/内联样式）的绝对与协议相对地址改写进代理：
  //    跨主机静态资源若直连（如 v.qq.com 频道页的 //vfiles.gtimg.cn/...），
  //    模块脚本会因 CORS（Origin 是 127.0.0.1:7180）被 CDN 拒绝，页面渲染直接断掉。
  html = rewriteSubresources(html, realUrl);

  const head = [];
  head.push('<meta charset="utf-8">');
  /* 注意：镜像路径模式下绝不注入 <base> 标签！
   * vue-router 的 createWebHistory 无 base 参数时会读取 <base> 标签作为应用基路径，
   * 导致当前路径被错误剥离（/c/music/ 被剥成 /）→ 匹配 catchAll → B 站分区页
   * 显示"此分区不存在"。镜像方案下代理路径与真实路径一致，相对资源天然正确，
   * 未被钩住的裸路径请求由 302 兜底还原真实主机，无需 base。 */
  head.push(buildInjectScript(realUrl));

  const block = head.join('\n');
  if (/<head[^>]*>/i.test(html)) {
    html = html.replace(/<head([^>]*)>/i, (m) => m + '\n' + block);
  } else if (/<html[^>]*>/i.test(html)) {
    html = html.replace(/<html([^>]*)>/i, (m) => m + '\n<head>' + block + '</head>');
  } else {
    html = '<!DOCTYPE html><html><head>' + block + '</head><body>' + html + '</body></html>';
  }
  return html;
}

/* ------------------------------------------------------------------ *
 * 错误页
 * ------------------------------------------------------------------ */
function sendErrorPage(res, code, title, detail) {
  const html =
    '<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8">' +
    '<title>' + title + '</title><style>' +
    'html,body{height:100%;margin:0}body{display:flex;align-items:center;justify-content:center;' +
    'background:#f7f8fa;color:#1b1d21;font-family:-apple-system,"Segoe UI","Microsoft YaHei",sans-serif}' +
    '.box{max-width:520px;padding:36px;text-align:center}' +
    '.ico{width:64px;height:64px;border-radius:20px;background:linear-gradient(135deg,#6b93ff,#3b6cf6);' +
    'display:flex;align-items:center;justify-content:center;margin:0 auto 20px;font-size:30px;color:#fff}' +
    'h1{font-size:19px;margin:0 0 10px}p{color:#70757f;font-size:13.5px;line-height:1.8;margin:0}' +
    'code{background:#eceff4;padding:2px 7px;border-radius:5px;font-size:12px;color:#3b6cf6}' +
    '</style></head><body><div class="box">' +
    '<div class="ico">&#9888;</div><h1>' + title + '</h1><p>' + detail + '</p></div></body></html>';
  res.writeHead(code, {
    'content-type': 'text/html; charset=utf-8',
    'content-length': Buffer.byteLength(html),
    'cache-control': 'no-store',
  });
  res.end(html);
}

/* ------------------------------------------------------------------ *
 * 需要剥离的响应头
 * ------------------------------------------------------------------ */
const STRIP_HEADERS = new Set([
  'x-frame-options',
  'content-security-policy',
  'content-security-policy-report-only',
  'x-content-security-policy',
  'cross-origin-opener-policy',
  'cross-origin-embedder-policy',
  'cross-origin-resource-policy',
  'permissions-policy',
  'feature-policy',
  'strict-transport-security',
  'alt-svc',
  'report-to',
  'nel',
  'expect-ct',
  'set-cookie',
  'transfer-encoding',
  'connection',
  'keep-alive',
  'public-key-pins',
]);

/* 不透传的客户端请求头（其余全部原样转发，保留 X-CSRF 等自定义头） */
const DROP_REQ_HEADERS = new Set([
  'host', 'connection', 'keep-alive', 'proxy-connection', 'te', 'trailer',
  'transfer-encoding', 'upgrade', 'content-length', 'accept-encoding',
  'cookie', 'origin', 'referer', 'upgrade-insecure-requests',
  'x-nova-ref', 'x-nova-ck-set',
]);

/* 解开可能存在的"套娃"镜像包装：自身代理 URL 里的 __nova_url 逐层解码 */
function unwrapSelf(host, url) {
  let out = String(url || '');
  const prefixes = ['http://' + host + '/', 'https://' + host + '/'];
  for (let g = 0; g < 5; g++) {
    if (!prefixes.some((p) => out.startsWith(p))) break;
    const m = /[?&]__nova_url=([^&]+)/.exec(out);
    if (!m) break;
    try { out = decodeURIComponent(m[1]); } catch (e) { break; }
  }
  return out;
}

function buildUpstreamHeaders(clientReq, u, bodyBuf) {
  const headers = {};
  for (const [k, v] of Object.entries(clientReq.headers)) {
    const lk = k.toLowerCase();
    if (DROP_REQ_HEADERS.has(lk)) continue;
    /* 客户端提示与 Fetch 元数据要原样转发：真实 Chrome 必发 sec-ch-ua* / sec-fetch-*，
     * 全丢会与 UA 自相矛盾，风控（阿里 um.js 等）会据此加风险分、提高验证码频率。 */
    if (lk.startsWith('sec-ch-ua') || lk.startsWith('sec-fetch-')) { headers[lk] = v; continue; }
    if (lk.startsWith('sec-') || lk.startsWith('proxy-')) continue;
    headers[lk] = v;
  }

  headers['user-agent'] = (clientReq.headers['user-agent'] || UA).replace(/HeadlessChrome/gi, 'Chrome');
  /* B 站视频 CDN（bilivideo/mountaintoys 等）实测校验「桌面 UA + www.bilibili.com Referer」：
   * 手机 UA 或 m 站 Referer 一律 403（mcdn PCDN 节点宽容，但 playurl 常返回传统节点）。
   * CDN 只看 UA/Referer 字段，统一按桌面 www 站身份请求即可，与客户端真实形态无关。 */
  if (/(^|\.)(bilivideo\.(com|cn)|mountaintoys\.cn|szbdyd\.com)$/i.test(u.hostname)) {
    headers['user-agent'] = UA;
    headers['referer'] = 'https://www.bilibili.com/';
  }
  /* 注意：不要对 bilibili 用 App UA！m.bilibili.com 检测到 bilibili_android 会认为
   * 自己在 App WebView 里，原生桥接失败后用"APP内尽享高清流畅视频/去打开"遮罩盖住播放器。
   * 普通手机浏览器 UA 才是 m 站可直接网页内播放的变体。 */
  headers['accept'] =
    clientReq.headers['accept'] ||
    'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8';
  headers['accept-language'] = clientReq.headers['accept-language'] || 'zh-CN,zh;q=0.9,en;q=0.8';
  headers['accept-encoding'] = 'gzip, deflate, br';
  /* 诊断模式下风控接口不压缩，日志里才能还原服务端返回的判定内容 */
  if (DIAG && /_____tmd_____|hamlet\/async|\/h5\/mtop/i.test(u.pathname)) {
    headers['accept-encoding'] = 'identity';
  }

  /* Referer / Origin 还原为真实页面地址。
   * 注意：绝不能引用未定义的 req（历史 bug），否则还原失败会退化成"合成的目标域名 Referer"，
   * 风控网关（阿里 _____tmd_____ 等）收到自指向 Referer 会判定请求被篡改。 */
  let realRef = null;
  const ref = clientReq.headers['referer'];
  if (ref) {
    try {
      const ru = new URL(ref);
      const nt = ru.searchParams.get('__nova_url');
      if (nt) {
        realRef = unwrapSelf(clientReq.headers.host || '', nt);
      } else if (ru.pathname === '/__p') {
        const target = ru.searchParams.get('url');
        if (target) realRef = target;
      } else if (/^https?:/i.test(ref) && !/^(127\.0\.0\.1|localhost)$/i.test(ru.hostname)) {
        realRef = ref;
      }
    } catch (e) { /* ignore */ }
  }

  /* 页面注入的提示头：真实页面地址（Referer 被站点策略抑制时也能算出正确的来源关系） */
  let pageUrl = null;
  const refHint = clientReq.headers['x-nova-ref'];
  if (refHint) {
    try {
      const t = decodeURIComponent(String(refHint));
      if (/^https?:/i.test(t)) pageUrl = t;
    } catch (e) { /* ignore */ }
  }
  if (!pageUrl && realRef) pageUrl = realRef;

  /* 原生 <script>/<iframe> 子请求没有 x-nova-ref：改写时真实页面地址放在 __nova_ref 参数里。
   * 浏览器对跨源子请求的 Referer 只发裸源（http://127.0.0.1:7180/），解不出页面地址，
   * 没有这个兜底时上游会看到代理域名 Referer，被验证码 SDK 的域名绑定校验拒绝。 */
  if (!pageUrl) {
    try {
      const t = new URL(clientReq.url, 'http://x').searchParams.get('__nova_ref');
      if (t && /^https?:/i.test(t)) { pageUrl = t; if (!realRef) realRef = t; }
    } catch (e) { /* ignore */ }
  }

  /* 客户端本地刚写入的 Cookie 立即并入 Jar（反爬的 Cookie 能力探测要求同步可见） */
  const ckSet = clientReq.headers['x-nova-ck-set'];
  if (ckSet) {
    try {
      let ckHost = u.hostname;
      if (pageUrl) { try { ckHost = new URL(pageUrl).hostname; } catch (e) { /* ignore */ } }
      decodeURIComponent(String(ckSet)).split('\n').forEach((line) => {
        const c = parseSetCookie(line.trim());
        if (!c) return;
        const j = jarOf(jarKeyFor(ckHost, c.domain));
        if (c.dead) j.delete(c.name);
        else j.set(c.name, c.value);
      });
    } catch (e) { /* ignore */ }
  }

  if (realRef) {
    /* 同源发完整地址，跨源只发 origin —— 与浏览器默认策略（strict-origin-when-cross-origin）一致 */
    let rf = realRef;
    try {
      const pr = new URL(realRef);
      rf = pr.hostname === u.hostname ? realRef : pr.origin + '/';
    } catch (e) { /* keep realRef */ }
    /* realHref 可能含非 ASCII（如中文搜索词），HTTP 头只允许 ASCII，否则 setHeader 抛
     * ERR_INVALID_CHAR 并打挂整个服务进程；encodeURI 不重编码已有百分号，兼容原样透传 */
    headers['referer'] = /^[\x00-\x7f]*$/.test(rf) ? rf : encodeURI(rf);
  }
  /* 客户端没发 Referer 就不合成：真实浏览器不发时上游也应看不到（合成目标域名会触发风控） */
  if ((clientReq.method || 'GET') !== 'GET') {
    if (pageUrl) {
      try { headers['origin'] = new URL(pageUrl).origin; } catch (e) { /* ignore */ }
    }
    if (!headers['origin']) headers['origin'] = u.origin;
  }
  /* sec-fetch-site 按真实来源关系重算：代理下浏览器只能报 same-origin，与真实站点关系不符 */
  if (headers['sec-fetch-site'] && pageUrl) {
    try {
      const ph = new URL(pageUrl).hostname;
      headers['sec-fetch-site'] =
        ph === u.hostname
          ? 'same-origin'
          : baseDomainOf(ph) === baseDomainOf(u.hostname)
            ? 'same-site'
            : 'cross-site';
    } catch (e) { /* ignore */ }
  }

  if (clientReq.headers['range']) headers['range'] = clientReq.headers['range'];

  const ck = cookieHeaderFor(u.hostname);
  if (ck) headers['cookie'] = ck;

  if (bodyBuf && bodyBuf.length) {
    headers['content-type'] =
      clientReq.headers['content-type'] || 'application/x-www-form-urlencoded';
    headers['content-length'] = bodyBuf.length;
  }
  return headers;
}

/* ------------------------------------------------------------------ *
 * 代理主流程
 * ------------------------------------------------------------------ */
function proxyRequest(clientReq, clientRes, targetUrl, depth, method, bodyBuf) {
  let u;
  try {
    u = new URL(targetUrl);
  } catch (e) {
    return sendErrorPage(clientRes, 400, '网址格式不正确', '请检查地址：<code>' + targetUrl + '</code>');
  }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') {
    return sendErrorPage(clientRes, 400, '不支持的协议', '仅支持 <code>http</code> 与 <code>https</code>。');
  }
  if (PUBLIC_MODE) {
    const bad = blockedTargetSync(u);
    if (bad) {
      diag({ blocked: (u.host + u.pathname).slice(0, 140), why: bad });
      return sendErrorPage(
        clientRes,
        403,
        '该地址不可访问',
        '公网模式下不代理内网 / 保留网段地址（' + bad + '）。'
      );
    }
  }

  const lib = u.protocol === 'https:' ? https : http;
  const headers = buildUpstreamHeaders(clientReq, u, bodyBuf);
  rememberLastOrigin(clientReq, u);

  diag({
    req: (u.host + u.pathname).slice(0, 140),
    q: (u.search || '').slice(0, /_____tmd_____/.test(u.pathname) ? 1400 : 140),
    m: method || 'GET',
    ck: ckNames(headers['cookie']),
    ref: String(headers['referer'] || '').slice(0, 120),
    or: headers['origin'] ? String(headers['origin']).slice(0, 60) : undefined,
    sfs: headers['sec-fetch-site'] || undefined,
    dest: clientReq.headers['sec-fetch-dest'] || undefined,
    mode: clientReq.headers['sec-fetch-mode'] || undefined,
  });

  const preq = lib.request(
    {
      protocol: u.protocol,
      hostname: u.hostname,
      port: u.port || undefined,
      path: u.pathname + u.search,
      method: method || 'GET',
      headers,
      servername: u.hostname,
      lookup: PUBLIC_MODE ? safeLookup : undefined,
    },
    (pres) => {
      const code = pres.statusCode || 200;
      if ([301, 302, 303, 307, 308].includes(code) && pres.headers.location && depth < 8) {
        /* 关键：重定向响应里的 Set-Cookie 必须落罐（风控验证通过凭证 x5sec 就是这么下发的），
         * 原来直接 resume() 丢弃，导致"验证通过→凭证丢失→立即重新挑战"。 */
        storeCookies(u.hostname, pres.headers['set-cookie']);
        captureRiskCookies(u.hostname, pres.headers);
        diag({
          res: (u.host + u.pathname).slice(0, 140),
          st: code,
          setck: setCkNames(pres.headers['set-cookie']),
          loc: String(pres.headers.location).slice(0, 160),
          redirect: 1,
        });
        pres.resume();
        let next;
        try {
          next = new URL(pres.headers.location, targetUrl).toString();
        } catch (e) {
          return sendErrorPage(clientRes, 502, '跳转地址无效', '目标站点返回了无法解析的跳转地址。');
        }
        const nm = code === 307 || code === 308 ? method : 'GET';
        return proxyRequest(clientReq, clientRes, next, depth + 1, nm, nm === 'GET' ? null : bodyBuf);
      }
      return handleUpstream(pres, clientRes, u, clientReq);
    }
  );

  preq.on('error', (err) => {
    if (!clientRes.headersSent) {
      if (err && err.code === 'ENOVA_BLOCKED') {
        return sendErrorPage(clientRes, 403, '该地址不可访问', '目标域名解析到内网 / 保留网段，公网模式下已拒绝。');
      }
      sendErrorPage(
        clientRes,
        502,
        '无法连接到该网站',
        '目标站点没有响应或拒绝了连接。<br>错误：<code>' +
          String(err.message || err).slice(0, 160) +
          '</code><br><br>请检查网络，或稍后重试。'
      );
    } else {
      clientRes.end();
    }
  });
  preq.setTimeout(35000, () => preq.destroy(new Error('请求超时（35s）')));

  if (bodyBuf && bodyBuf.length) preq.end(bodyBuf);
  else preq.end();
}

function handleUpstream(pres, res, u, clientReq) {
  storeCookies(u.hostname, pres.headers['set-cookie']);
  captureRiskCookies(u.hostname, pres.headers);
  mediaRecord(u, pres, clientReq);
  diag({
    res: (u.host + u.pathname).slice(0, 140),
    st: pres.statusCode,
    setck: setCkNames(pres.headers['set-cookie']),
    loc: pres.headers['location'] ? String(pres.headers['location']).slice(0, 160) : undefined,
  });

  const ct = String(pres.headers['content-type'] || '').toLowerCase();
  const isHtml = ct.includes('text/html') || ct.includes('application/xhtml+xml');

  /* 手机端访问 www.bilibili.com 主站页面：302 到移动版 m.bilibili.com。
   * m 站是 H5 页面（自带可播的移动版播放器），比桌面版在手机上体验好得多；
   * 配合 B 站 App UA，番剧页直接给出 H5 播放器。仅重定向播放相关路径，避免 m 站不存在的路径 404。 */
  const __mobUA =
    clientReq && clientReq.headers['user-agent'] &&
    /Android|iPhone|iPad|Mobile/i.test(clientReq.headers['user-agent']);
  if (
    isHtml &&
    pres.statusCode === 200 &&
    __mobUA &&
    u.hostname === 'www.bilibili.com' &&
    /^(\/|\/index\.html|\/video\/|\/bangumi\/play\/|\/cheese\/play\/|\/opus\/|\/dynamic\/|\/festival\/)/.test(u.pathname)
  ) {
    const mUrl = 'https://m.bilibili.com' + u.pathname + u.search;
    try {
      res.writeHead(302, { location: proxyUrlFor(mUrl), 'cache-control': 'no-store' });
      diag({ rewrites: 'm-bili', from: u.href.slice(0, 120) });
    } catch (e) { /* ignore */ }
    res.end();
    pres.destroy();
    return;
  }

  /* 手机端 m 站首页/视频页的"外链播放器" iframe（player.bilibili.com/player.html）
   * 在代理内 core.js 不发 playurl（依赖与父页面的 postMessage 握手，代理环境握手失败），
   * 播放器区域永远转圈。直接 302 到 m.bilibili.com 视频页——页面内嵌 H5 播放器，已验证可播。 */
  if (
    isHtml &&
    pres.statusCode === 200 &&
    __mobUA &&
    u.hostname === 'player.bilibili.com' &&
    u.pathname === '/player.html'
  ) {
    const bvid = u.searchParams.get('bvid');
    const aid = u.searchParams.get('aid');
    if (bvid || aid) {
      const mUrl =
        'https://m.bilibili.com/video/' + (bvid ? bvid : 'av' + aid) + '?_nova_p2v=1';
      try {
        res.writeHead(302, { location: proxyUrlFor(mUrl), 'cache-control': 'no-store' });
        diag({ rewrites: 'bili-player2video', from: u.href.slice(0, 140) });
      } catch (e) { /* ignore */ }
      res.end();
      pres.destroy();
      return;
    }
  }

  const out = {};
  for (const [k, v] of Object.entries(pres.headers)) {
    if (STRIP_HEADERS.has(k)) continue;
    out[k] = v;
  }
  out['access-control-allow-origin'] = '*';
  out['access-control-allow-headers'] = '*';
  out['access-control-allow-methods'] = 'GET,POST,PUT,DELETE,OPTIONS,PATCH';
  out['access-control-expose-headers'] = '*';
  /* 本次响应后该站点的 Cookie 快照：页面 JS 拿到响应即可同步看到新 Cookie
   * （风控要求"写 cookie 立即可见"，异步回包会错过验证时点） */
  try {
    const ckSnap = cookieHeaderFor(u.hostname);
    if (ckSnap && ckSnap.length < 3000) out['x-nova-ck'] = encodeURIComponent(ckSnap);
  } catch (e) { /* ignore */ }

  if (!isHtml) {
    // 二进制 / 流媒体：原样透传，保留 Range 相关头，视频进度可拖动
    if (!out['cache-control']) out['cache-control'] = 'public, max-age=300';
    /* CSS 特殊处理：内部绝对/协议相对 url() 若不改写会直连真实网络，
     * 字体等资源因 CORS（CDN 不认代理 Origin）静默失败。无 Range 请求时
     * 解码改写后再输出；Range 场景（少见）保持原样透传。 */
    if (
      ct.includes('text/css') &&
      clientReq && !clientReq.headers.range &&
      pres.statusCode === 200
    ) {
      const cssChunks = [];
      const cssStream = decodeBody(pres);
      cssStream.on('data', (c) => cssChunks.push(c));
      cssStream.on('error', () => res.end());
      cssStream.on('end', () => {
        try {
          const raw = Buffer.concat(cssChunks);
          let css = decodeText(raw, detectCharset(raw, pres.headers['content-type']));
          css = rewriteCssUrls(css, u.toString());
          const buf = Buffer.from(css, 'utf8');
          delete out['content-encoding'];
          delete out['content-length'];
          out['content-type'] = 'text/css; charset=utf-8';
          out['content-length'] = buf.length;
          res.writeHead(pres.statusCode || 200, out);
          res.end(buf);
        } catch (e) {
          res.end();
        }
      });
      return;
    }
    /* m3u8 播放列表：内容里的分片/子列表/KEY URI 改写进代理，
     * 否则页面内 hls.js 相对解析丢 __nova_url → 分片 404 黑屏。
     * 注意：部分源站（fengbao12 等）对 m3u8 也返回 206，勿用 st===200 / 无 Range 限制 */
    if (
      (pres.statusCode === 200 || pres.statusCode === 206) &&
      (ct.includes('mpegurl') || /\.m3u8($|\?)/i.test(u.pathname + u.search))
    ) {
      const m3Chunks = [];
      const m3Stream = decodeBody(pres);
      m3Stream.on('data', (c) => m3Chunks.push(c));
      m3Stream.on('error', () => res.end());
      m3Stream.on('end', () => {
        try {
          const raw = Buffer.concat(m3Chunks);
          const text = Buffer.from(
            rewriteM3u8(decodeText(raw, 'utf8'), u.toString()),
            'utf8'
          );
          delete out['content-encoding'];
          delete out['content-length'];
          out['content-type'] = 'application/vnd.apple.mpegurl';
          out['content-length'] = text.length;
          out['cache-control'] = 'no-store';
          res.writeHead(pres.statusCode || 200, out);
          res.end(text);
          diag({ rewrites: 'm3u8', url: u.href.slice(0, 120), lines: text.length });
        } catch (e) {
          res.end();
        }
      });
      return;
    }
    /* 诊断：风控接口的响应体是判定依据（为何持续要求验证），采样记入日志 */
    if (DIAG && /_____tmd_____|hamlet\/async|\/h5\/mtop/i.test(u.pathname)) {
      const bufs = [];
      let n = 0;
      pres.on('data', (c) => {
        if (n < 3000) { bufs.push(c); n += c.length; }
      });
      pres.on('end', () => {
        try {
          const body = Buffer.concat(bufs).toString('utf8').replace(/\s+/g, ' ').slice(0, 2000);
          diag({ body: (u.host + u.pathname).slice(0, 120), st: pres.statusCode, preview: body });
        } catch (e) { /* ignore */ }
      });
    }
    res.writeHead(pres.statusCode || 200, out);
    pres.pipe(res);
    pres.on('error', () => res.end());
    return;
  }

  // HTML：解压 -> 重写 -> 以 utf-8 重新输出
  // 注意：非 HTML 分支必须保留 content-encoding / content-length，
  // 否则浏览器收不到解压提示，XHR/fetch 拿到的就是乱码。
  delete out['content-encoding'];
  delete out['content-length'];
  delete out['content-range'];
  delete out['accept-ranges'];
  delete out.etag;
  delete out['last-modified'];
  out['content-type'] = 'text/html; charset=utf-8';
  out['cache-control'] = 'no-store';

  const chunks = [];
  const stream = decodeBody(pres);
  stream.on('data', (c) => chunks.push(c));
  stream.on('error', () => {
    if (!res.headersSent) sendErrorPage(res, 502, '页面内容解析失败', '目标站点返回了无法解码的内容。');
    else res.end();
  });
  stream.on('end', () => {
    try {
      const raw = Buffer.concat(chunks);
      const charset = detectCharset(raw, pres.headers['content-type']);
      let html = decodeText(raw, charset);
      /* 诊断：风控/验证码 iframe 文档是 HTML，原样存档便于分析其通信方式 */
      if (DIAG && /_____tmd_____|hamlet\/async|\/h5\/mtop/i.test(u.pathname)) {
        try {
          fs.writeFileSync(
            DIAG_FILE.replace(/\.log$/, '') + '-tmd.html',
            '<!-- ' + u.href + ' -->\n' + html
          );
        } catch (e) { /* ignore */ }
        diag({
          body: (u.host + u.pathname).slice(0, 120),
          st: pres.statusCode,
          ctype: pres.headers['content-type'],
          isHtml: 1,
          preview: html.replace(/\s+/g, ' ').slice(0, 2000),
        });
      }
      html = rewriteHtml(html, u.toString());
      const buf = Buffer.from(html, 'utf8');
      out['content-length'] = buf.length;
      res.writeHead(pres.statusCode || 200, out);
      res.end(buf);
    } catch (e) {
      if (!res.headersSent)
        sendErrorPage(res, 502, '页面处理出错', '错误：<code>' + String(e.message).slice(0, 160) + '</code>');
      else res.end();
    }
  });
}

/* ------------------------------------------------------------------ *
 * favicon 代理
 * ------------------------------------------------------------------ */
function proxyFavicon(target, res) {
  let u;
  try {
    u = new URL(target);
  } catch (e) {
    res.writeHead(404).end();
    return;
  }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') {
    /* 页面可能送来 nova:/chrome:/about: 等自定义协议的 favicon 地址，
     * 直接 404，避免 http.request 抛 ERR_INVALID_PROTOCOL 打挂整个服务。 */
    res.writeHead(404).end();
    return;
  }
  if (PUBLIC_MODE && blockedTargetSync(u)) {
    res.writeHead(404).end();
    return;
  }
  const lib = u.protocol === 'https:' ? https : http;
  const req = lib.request(
    {
      protocol: u.protocol,
      hostname: u.hostname,
      port: u.port || undefined,
      path: '/favicon.ico',
      method: 'GET',
      headers: { 'user-agent': UA, accept: 'image/*,*/*;q=0.8', referer: u.origin + '/' },
      servername: u.hostname,
      lookup: PUBLIC_MODE ? safeLookup : undefined,
    },
    (r) => {
      if (r.statusCode !== 200) {
        r.resume();
        res.writeHead(404).end();
        return;
      }
      res.writeHead(200, {
        'content-type': r.headers['content-type'] || 'image/x-icon',
        'cache-control': 'public, max-age=86400',
      });
      r.pipe(res);
    }
  );
  req.on('error', () => res.writeHead(404).end());
  req.setTimeout(6000, () => req.destroy());
  req.end();
}

/* ------------------------------------------------------------------ *
 * 静态资源 + 路由
 * ------------------------------------------------------------------ */
const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.ico': 'image/x-icon',
  '.woff2': 'font/woff2',
  '.mp4': 'video/mp4',
};

function serveStatic(req, res, file) {
  const full = path.join(ROOT, file);
  if (!full.startsWith(ROOT)) return res.writeHead(403).end();
  fs.readFile(full, (err, data) => {
    if (err) return res.writeHead(404).end('Not found');
    if (file === 'index.html') {
      /* 注入"由本服务提供"标记：前端据此判定代理模式。
       * 此前前端用 hostname 是否为 localhost 判断，手机经局域网 IP 访问会被误判为静态托管模式。 */
      const html = data.toString('utf8').replace('<head>', '<head><script>window.__NOVA_PROXY_SERVER__=1;</script>');
      data = Buffer.from(html, 'utf8');
    }
    res.writeHead(200, {
      'content-type': MIME[path.extname(full).toLowerCase()] || 'application/octet-stream',
      'cache-control': 'no-cache',
    });
    res.end(data);
  });
}

/* 页面侧行为日志：postMessage / cookie 读写 / 框架状态，仅诊断模式记录 */
function handlePageLog(req, res, parsed) {
  const o = parsed.searchParams.get('o');
  const t = parsed.searchParams.get('t');
  if (!o || !t || t !== ckToken(o)) { res.writeHead(204).end(); return; }
  if (req.method !== 'POST') { res.writeHead(204).end(); return; }
  let body = '';
  req.on('data', (c) => {
    body += c;
    if (body.length > 65536) req.destroy();
  });
  req.on('end', () => {
    let host = '';
    try { host = new URL(o).hostname; } catch (e) { /* ignore */ }
    if (DIAG) {
      body.split('\n').slice(0, 80).forEach((line) => {
        const v = String(line).trim();
        if (v.endsWith('\\r')) { /* 去掉 CRLF 残留 */ }
        const clean = v.replace(/\r$/, '');
        if (clean) diag({ page: host, ev: clean.slice(0, 320) });
      });
    }
    res.writeHead(204, { 'access-control-allow-origin': '*' }).end();
  });
  req.on('error', () => res.end());
}

function handleCookieSync(req, res, parsed) {
  const o = parsed.searchParams.get('o');
  const t = parsed.searchParams.get('t');
  if (!o || !t) return res.writeHead(400).end();
  if (t !== ckToken(o)) return res.writeHead(403).end();
  let host = '';
  try { host = new URL(o).hostname; } catch (e) { return res.writeHead(400).end(); }

  if (req.method === 'POST') {
    let body = '';
    req.on('data', (c) => {
      body += c;
      if (body.length > 65536) req.destroy();
    });
    req.on('end', () => {
      body.split('\n').forEach((line) => {
        const c = parseSetCookie(line.trim());
        if (!c) return;
        const j = jarOf(jarKeyFor(host, c.domain));
        if (c.dead) j.delete(c.name);
        else j.set(c.name, c.value);
      });
      res.writeHead(204).end();
    });
    req.on('error', () => res.end());
    return;
  }

  res.writeHead(200, {
    'content-type': 'text/plain; charset=utf-8',
    'cache-control': 'no-store',
    'access-control-allow-origin': '*',
  });
  res.end(cookieHeaderFor(host));
}

/* ------------------------------------------------------------------ *
 * 下载管理器：真实落盘 + 进度 + 暂停/续传 + 任务持久化
 * 走同一套 Cookie Jar 与 Referer 还原，带站点登录态下载
 * ------------------------------------------------------------------ */
const DL_DIR = path.join(ROOT, 'downloads');
const DL_INDEX = path.join(DL_DIR, 'index.json');
const DL_MAX_ACTIVE = 3;
const dlJobs = new Map(); // id -> job
const dlQueue = [];
let dlIdxTimer = null;

function dlLoad() {
  try {
    const arr = JSON.parse(fs.readFileSync(DL_INDEX, 'utf8'));
    if (Array.isArray(arr)) {
      arr.forEach((j) => {
        if (!j || j.id == null) return;
        /* 上次退出时还在下载的任务标记为"已暂停"，文件 .part 还在，可断点续传 */
        if (j.status === 'downloading') j.status = 'paused';
        delete j.speed;
        dlJobs.set(String(j.id), j);
      });
    }
  } catch (e) { /* 首次运行还没有索引文件 */ }
}
function dlSave() {
  if (dlIdxTimer) return;
  dlIdxTimer = setTimeout(() => {
    dlIdxTimer = null;
    try {
      fs.mkdirSync(DL_DIR, { recursive: true });
      const arr = [...dlJobs.values()].map((j) => ({
        id: j.id, url: j.url, ref: j.ref || '', name: j.name, file: j.file || '',
        total: j.total || 0, received: j.received || 0, status: j.status,
        error: j.error || '', mime: j.mime || '', ts: j.ts || 0, doneTs: j.doneTs || 0,
        segDone: j.segDone || 0, note: j.note || '',
      }));
      fs.writeFileSync(DL_INDEX, JSON.stringify(arr));
    } catch (e) { /* ignore */ }
  }, 400);
}
function dlPublic(j) {
  return {
    id: j.id, url: j.url, ref: j.ref || '', name: j.name, file: j.file || '',
    total: j.total || 0, received: j.received || 0, status: j.status,
    error: j.error || '', speed: j.speed || 0, mime: j.mime || '',
    ts: j.ts || 0, doneTs: j.doneTs || 0, note: j.note || '',
  };
}
function dlList() {
  const rank = { downloading: 0, paused: 1, error: 2, done: 3 };
  return [...dlJobs.values()]
    .sort((a, b) => (rank[a.status] ?? 9) - (rank[b.status] ?? 9) || (b.ts || 0) - (a.ts || 0))
    .map(dlPublic);
}
function dlSanitizeName(s) {
  let n = String(s || '').trim();
  n = n.split(/[\\/]/).pop() || '';
  n = n.replace(/[\x00-\x1f<>:"|?*]/g, '').replace(/^\.+/, '').trim();
  if (!n) n = 'download-' + new Date().toISOString().slice(0, 10) + '.bin';
  if (n.length > 120) {
    const dot = n.lastIndexOf('.');
    const ext = dot > 0 ? n.slice(dot) : '';
    n = n.slice(0, 120 - ext.length) + ext;
  }
  return n;
}
function dlUniquePath(name) {
  let p = path.join(DL_DIR, name);
  if (!fs.existsSync(p)) return name;
  const dot = name.lastIndexOf('.');
  const base = dot > 0 ? name.slice(0, dot) : name;
  const ext = dot > 0 ? name.slice(dot) : '';
  for (let i = 1; i < 999; i++) {
    const n2 = base + ' (' + i + ')' + ext;
    if (!fs.existsSync(path.join(DL_DIR, n2))) return n2;
  }
  return Date.now() + '_' + name;
}
function dlNameFromDisp(cd) {
  if (!cd) return '';
  let m = /filename\*\s*=\s*(?:utf-8|UTF-8)''([^;]+)/.exec(cd);
  if (m) { try { return decodeURIComponent(m[1].replace(/^["']|["']$/g, '')); } catch (e) {} }
  m = /filename\s*=\s*"([^"]+)"/.exec(cd) || /filename\s*=\s*([^;]+)/.exec(cd);
  if (m) { try { return decodeURIComponent(m[1].trim()); } catch (e) { return m[1].trim(); } }
  return '';
}
function dlStart(targetUrl, ref, nameHint) {
  let u;
  try { u = new URL(targetUrl); } catch (e) { return { err: '网址无效' }; }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') return { err: '仅支持 http/https 链接' };
  if (PUBLIC_MODE && blockedTargetSync(u)) return { err: '公网模式下不下载内网 / 保留网段地址' };
  const job = {
    id: 'd' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6),
    url: targetUrl, ref: String(ref || ''), name: nameHint ? dlSanitizeName(nameHint) : '',
    total: 0, received: 0, status: 'downloading', error: '', mime: '',
    ts: Date.now(), doneTs: 0, speed: 0, file: '',
  };
  dlJobs.set(job.id, job);
  dlSave();
  dlQueuePush(job.id);
  return { ok: true, job: dlPublic(job) };
}
function dlQueuePush(id) { dlQueue.push(id); dlPump(); }
function dlPump() {
  let active = 0;
  dlJobs.forEach((j) => { if (j.status === 'downloading') active++; });
  while (active < DL_MAX_ACTIVE && dlQueue.length) {
    const j = dlJobs.get(dlQueue.shift());
    if (!j || j.status !== 'downloading') continue;
    active++;
    dlFetch(j, j.received > 0 ? j.received : 0);
  }
}
function dlSettle(job) {
  if (job.__spd) { clearInterval(job.__spd); job.__spd = null; }
  delete job.req;
  job.speed = 0;
  dlSave();
  dlPump();
}
function dlFetch(job, fromByte) {
  /* m3u8：走 HLS 专用流程（解析播放列表、逐分片下载、AES-128 解密、合并） */
  if (/\.m3u8(?:[?#]|$)/i.test(String(job.url).split('#')[0])) return dlFetchHls(job);
  job.status = 'downloading';
  job.error = '';
  job.__lastReceived = job.received;
  job.__lastTs = Date.now();

  const fail = (msg) => {
    if (job.status !== 'downloading') return;
    job.status = 'error';
    job.error = String(msg).slice(0, 200);
    try { if (job.ws) job.ws.close(); } catch (e) { /* ignore */ }
    dlSettle(job);
  };
  const refererFor = (host) => {
    try {
      if (!job.ref || !/^https?:/i.test(job.ref)) return '';
      const pr = new URL(job.ref);
      return pr.hostname === host ? job.ref : pr.origin + '/';
    } catch (e) { return ''; }
  };

  function request(curUrl, depth) {
    if (job.status !== 'downloading') return;
    let cu;
    try { cu = new URL(curUrl); } catch (e) { return fail('网址无效'); }
    const lib = cu.protocol === 'https:' ? https : http;
    const headers = { 'user-agent': UA, accept: '*/*', 'accept-encoding': 'identity' };
    const ck = cookieHeaderFor(cu.hostname);
    if (ck) headers.cookie = ck;
    const rf = refererFor(cu.hostname);
    if (rf) headers.referer = /^[\x00-\x7f]*$/.test(rf) ? rf : encodeURI(rf);
    if (fromByte > 0) headers.range = 'bytes=' + fromByte + '-';

    const req = lib.request(
      {
        protocol: cu.protocol, hostname: cu.hostname, port: cu.port || undefined,
        path: cu.pathname + cu.search, method: 'GET', headers, servername: cu.hostname,
        lookup: PUBLIC_MODE ? safeLookup : undefined,
      },
      (pres) => {
        /* 暂停/取消发生在响应到达之前时，响应此刻才回来：直接丢弃，不落盘 */
        if (job.status !== 'downloading') { pres.resume(); return; }
        const code = pres.statusCode || 0;
        if ([301, 302, 303, 307, 308].includes(code) && pres.headers.location && depth < 8) {
          pres.resume();
          try { return request(new URL(pres.headers.location, cu).toString(), depth + 1); }
          catch (e) { return fail('跳转地址无效'); }
        }
        if (code < 200 || code >= 300) { pres.resume(); return fail('HTTP ' + code); }

        job.mime = String(pres.headers['content-type'] || '').split(';')[0].trim();

        /* 文件名：页面提示 > Content-Disposition > URL 路径 > 兜底 */
        if (!job.name || /^(download|download-\d{4}-\d{2}-\d{2})/.test(job.name.split('.')[0])) {
          let nm = dlNameFromDisp(pres.headers['content-disposition']);
          if (!nm) {
            try {
              const bp = decodeURIComponent(cu.pathname.split('/').pop() || '').trim();
              if (bp && !bp.endsWith('/')) nm = bp;
            } catch (e) { /* ignore */ }
          }
          if (nm) job.name = dlSanitizeName(nm);
        }

        try { fs.mkdirSync(DL_DIR, { recursive: true }); } catch (e) { /* ignore */ }
        if (!job.file) job.file = dlUniquePath(job.name);
        const partPath = path.join(DL_DIR, job.file + '.part');
        const finalPath = path.join(DL_DIR, job.file);

        if (code === 206) {
          const cr = /bytes\s+\d+-\d+\/(\d+|\*)/i.exec(String(pres.headers['content-range'] || ''));
          job.total = cr && cr[1] !== '*' ? Number(cr[1]) : fromByte + (Number(pres.headers['content-length']) || 0);
        } else {
          /* 200：服务器不支持 Range，从头收（.part 截断重写） */
          fromByte = 0;
          job.received = 0;
          job.total = Number(pres.headers['content-length']) || 0;
        }

        job.received = fromByte;
        const ws = fs.createWriteStream(partPath, { flags: fromByte > 0 ? 'a' : 'w' });
        job.ws = ws;
        pres.on('data', (c) => { job.received += c.length; });
        pres.pipe(ws);
        pres.on('error', (e) => {
          try { ws.close(); } catch (e2) { /* ignore */ }
          fail('网络中断：' + (e && e.message ? e.message : '未知错误'));
        });
        ws.on('error', () => fail('磁盘写入失败'));
        const finish = () => {
          if (job.status !== 'downloading') return;
          try { fs.renameSync(partPath, finalPath); } catch (e) { return fail('保存文件失败'); }
          job.status = 'done';
          job.doneTs = Date.now();
          job.total = job.total || job.received;
          dlSettle(job);
        };
        ws.on('finish', finish);

        /* 速度采样（1s 窗口） */
        job.__spd = setInterval(() => {
          const now = Date.now();
          const dt = (now - (job.__lastTs || now)) / 1000;
          if (dt > 0) {
            job.speed = Math.max(0, Math.round((job.received - (job.__lastReceived || 0)) / dt));
            job.__lastReceived = job.received;
            job.__lastTs = now;
          }
        }, 1000);
        if (job.__spd.unref) job.__spd.unref();
      }
    );
    req.on('error', (e) => fail('连接失败：' + (e && e.message ? e.message : '未知错误')));
    /* 60s 无数据视为连接挂死：中断为 error，用户点"继续"可断点续传 */
    req.setTimeout(60000, () => req.destroy(new Error('连接超时（60s 无数据）')));
    req.end();
    /* 请求一创建就挂到任务上：暂停/取消在握手阶段到来时也能立刻销毁连接 */
    job.req = req;
  }
  request(job.url, 0);
}

/* ---------- HLS（m3u8）下载：分片顺序下载 -> 合并为 .ts，支持 AES-128 解密 ---------- */
function dlHlsGet(job, curUrl, depth, binary) {
  return new Promise((resolve, reject) => {
    let cu;
    try { cu = new URL(curUrl); } catch (e) { return reject(new Error('网址无效')); }
    const lib = cu.protocol === 'https:' ? https : http;
    const headers = { 'user-agent': UA, accept: '*/*', 'accept-encoding': 'identity' };
    const ck = cookieHeaderFor(cu.hostname);
    if (ck) headers.cookie = ck;
    try {
      if (job.ref && /^https?:/i.test(job.ref)) {
        const pr = new URL(job.ref);
        const rf = pr.hostname === cu.hostname ? job.ref : pr.origin + '/';
        headers.referer = /^[\x00-\x7f]*$/.test(rf) ? rf : encodeURI(rf);
      }
    } catch (e) { /* ignore */ }
    const req = lib.request(
      {
        protocol: cu.protocol, hostname: cu.hostname, port: cu.port || undefined,
        path: cu.pathname + cu.search, method: 'GET', headers, servername: cu.hostname,
        lookup: PUBLIC_MODE ? safeLookup : undefined,
      },
      (pres) => {
        /* 暂停/取消发生在响应到达之前：直接丢弃 */
        if (job.status !== 'downloading') { pres.resume(); return reject(new Error('已暂停')); }
        job.req = pres;
        const code = pres.statusCode || 0;
        if ([301, 302, 303, 307, 308].includes(code) && pres.headers.location && depth < 6) {
          pres.resume();
          try { return resolve(dlHlsGet(job, new URL(pres.headers.location, cu).toString(), depth + 1, binary)); }
          catch (e) { return reject(new Error('跳转地址无效')); }
        }
        if (code < 200 || code >= 300) { pres.resume(); return reject(new Error('HTTP ' + code)); }
        const chunks = [];
        const src = binary ? pres : decodeBody(pres);
        src.on('data', (c) => chunks.push(c));
        src.on('error', (e) => reject(new Error('网络中断：' + (e && e.message ? e.message : '未知错误'))));
        src.on('end', () => resolve(binary ? Buffer.concat(chunks) : Buffer.concat(chunks).toString('utf8')));
      }
    );
    req.on('error', (e) => reject(new Error('连接失败：' + (e && e.message ? e.message : '未知错误'))));
    req.setTimeout(45000, () => req.destroy(new Error('连接超时（45s）')));
    req.end();
    job.req = req;
  });
}
async function dlFetchHls(job) {
  const partPath = () => path.join(DL_DIR, job.file + '.part');
  const fail = (msg) => {
    if (job.status !== 'downloading') return; /* 暂停/取消时静默：segDone 断点保留 */
    job.status = 'error';
    job.error = String(msg).slice(0, 200);
    dlSettle(job);
  };
  try { fs.mkdirSync(DL_DIR, { recursive: true }); } catch (e) { /* ignore */ }
  if (!job.file) {
    let base = job.name || '';
    if (!base) {
      try { base = decodeURIComponent(new URL(job.url).pathname.split('/').pop() || '') || 'video'; }
      catch (e) { base = 'video'; }
    }
    base = (base.replace(/\.m3u8(?:\?.*)?$/i, '').trim() || 'video') + '.ts';
    job.name = dlSanitizeName(base);
    job.file = dlUniquePath(job.name);
    dlSave();
  }
  job.status = 'downloading';
  job.error = '';
  job.__lastReceived = job.received;
  job.__lastTs = Date.now();
  job.__spd = setInterval(() => {
    const now = Date.now();
    const dt = (now - (job.__lastTs || now)) / 1000;
    if (dt > 0) {
      job.speed = Math.max(0, Math.round((job.received - (job.__lastReceived || 0)) / dt));
      job.__lastReceived = job.received;
      job.__lastTs = now;
    }
  }, 1000);
  if (job.__spd.unref) job.__spd.unref();

  const keyCache = new Map();
  try {
    let plText = await dlHlsGet(job, job.url, 0, false);
    /* master 播放列表 -> 选最高码率的子列表（最多两层） */
    for (let i = 0; i < 2; i++) {
      if (!/#EXT-X-STREAM-INF/i.test(plText)) break;
      const lines = plText.split('\n');
      let best = '', bestBw = -1;
      for (let li = 0; li < lines.length; li++) {
        if (!/^#EXT-X-STREAM-INF/i.test(lines[li])) continue;
        const bw = Number((/BANDWIDTH=(\d+)/i.exec(lines[li]) || [])[1] || 0);
        const uri = (lines[li + 1] || '').trim();
        if (uri && !uri.startsWith('#') && bw > bestBw) { best = uri; bestBw = bw; }
      }
      if (!best) return fail('播放列表解析失败：没有可用的子流');
      plText = await dlHlsGet(job, new URL(best, job.url).toString(), 0, false);
    }
    if (!/#EXTINF/i.test(plText)) return fail('不是有效的媒体播放列表');
    if (!/#EXT-X-ENDLIST/i.test(plText)) return fail('直播流暂不支持下载');

    const lines = plText.split('\n').map((s) => s.trim());
    const seqBase = Number((/#EXT-X-MEDIA-SEQUENCE:(\d+)/i.exec(plText) || [])[1] || 0);
    let curKey = '', curIv = '';
    const segs = [];
    for (const line of lines) {
      if (/^#EXT-X-KEY/i.test(line)) {
        const method = ((/METHOD=([^,]+)/i.exec(line) || [])[1] || 'NONE').toUpperCase();
        const ku = /URI="([^"]+)"/i.exec(line);
        const ivm = /IV=0[xX]([0-9a-fA-F]+)/.exec(line);
        curKey = method === 'NONE' || !ku ? '' : new URL(ku[1], job.url).toString();
        curIv = ivm ? ivm[1] : '';
      } else if (line && !line.startsWith('#')) {
        segs.push({ url: new URL(line, job.url).toString(), key: curKey, iv: curIv });
      }
    }
    if (!segs.length) return fail('播放列表中没有分片');

    const segDone0 = Number(job.segDone) || 0;
    if (segDone0 > segs.length) { job.segDone = 0; dlSave(); }
    job.total = 0; /* 进度按分片数展示（note 字段），received 记录字节数 */
    job.note = '分片 ' + Math.min(Number(job.segDone) || 0, segs.length) + '/' + segs.length;
    dlSave();

    for (let i = Number(job.segDone) || 0; i < segs.length; i++) {
      if (job.status !== 'downloading') return; /* 暂停/取消：断点保留 */
      const sg = segs[i];
      let buf = await dlHlsGet(job, sg.url, 0, true);
      if (sg.key) {
        let keyBuf = keyCache.get(sg.key);
        if (!keyBuf) {
          keyBuf = await dlHlsGet(job, sg.key, 0, true);
          if (keyBuf.length !== 16) return fail('密钥长度异常，无法解密');
          keyCache.set(sg.key, keyBuf);
        }
        let ivBuf;
        if (sg.iv) {
          ivBuf = Buffer.from(sg.iv.length > 32 ? sg.iv.slice(-32) : sg.iv.padStart(32, '0'), 'hex');
        } else {
          ivBuf = Buffer.alloc(16);
          ivBuf.writeUInt32BE(seqBase + i, 12); /* 规范默认：IV = 媒体序列号 */
        }
        try {
          const dc = crypto.createDecipheriv('aes-128-cbc', keyBuf, ivBuf);
          buf = Buffer.concat([dc.update(buf), dc.final()]);
        } catch (e) {
          return fail('分片解密失败（' + (e && e.message ? e.message : e) + '）');
        }
      }
      fs.appendFileSync(partPath(), buf);
      job.received += buf.length;
      job.segDone = i + 1;
      job.note = '分片 ' + job.segDone + '/' + segs.length;
      if (i % 5 === 0) dlSave();
    }
    try { fs.renameSync(partPath(), path.join(DL_DIR, job.file)); } catch (e) { return fail('保存文件失败'); }
    job.status = 'done';
    job.doneTs = Date.now();
    job.total = job.received;
    job.mime = 'video/mp2t';
    dlSettle(job);
  } catch (e) {
    fail(String((e && e.message) || e));
  }
}
function dlPause(id) {
  const j = dlJobs.get(String(id));
  if (!j) return { err: '任务不存在' };
  if (j.status !== 'downloading') return { err: '任务不在下载中' };
  j.status = 'paused';
  try { if (j.req) j.req.destroy(); } catch (e) { /* ignore */ }
  dlSettle(j);
  dlSave();
  return { ok: true, job: dlPublic(j) };
}
function dlResume(id) {
  const j = dlJobs.get(String(id));
  if (!j) return { err: '任务不存在' };
  if (j.status !== 'paused' && j.status !== 'error') return { err: '当前状态无法继续' };
  /* .part 还在就断点续传；服务器不支持 Range 时会自动从头收 */
  j.status = 'downloading';
  j.error = '';
  dlSave();
  dlQueuePush(j.id);
  return { ok: true, job: dlPublic(j) };
}
function dlRemove(id, delFile) {
  const j = dlJobs.get(String(id));
  if (!j) return { err: '任务不存在' };
  if (j.status === 'downloading') {
    j.status = 'canceled';
    try { if (j.req) j.req.destroy(); } catch (e) { /* ignore */ }
    dlSettle(j);
  }
  if (delFile && j.file) {
    [j.file, j.file + '.part'].forEach((f) => {
      try { fs.unlinkSync(path.join(DL_DIR, f)); } catch (e) { /* ignore */ }
    });
  }
  dlJobs.delete(String(id));
  dlSave();
  return { ok: true };
}
function dlClearFinished() {
  [...dlJobs.values()].forEach((j) => {
    if (j.status === 'done' || j.status === 'error') dlJobs.delete(j.id);
  });
  dlSave();
  return { ok: true };
}
function dlServeFile(req, res, parsed) {
  const j = dlJobs.get(parsed.searchParams.get('id') || '');
  if (!j || !j.file) return res.writeHead(404).end('Not found');
  const fp = path.join(DL_DIR, j.file);
  let st;
  try { st = fs.statSync(fp); } catch (e) { return res.writeHead(404).end('文件不存在'); }
  const base = {
    'content-type': j.mime || 'application/octet-stream',
    'accept-ranges': 'bytes',
    'cache-control': 'no-store',
    'access-control-allow-origin': '*',
  };
  if (parsed.searchParams.get('dl') === '1') {
    base['content-disposition'] = "attachment; filename*=UTF-8''" + encodeURIComponent(j.name);
  }
  const m = /^bytes=(\d*)-(\d*)$/.exec(String(req.headers.range || ''));
  if (m) {
    let s = m[1] === '' ? 0 : Number(m[1]);
    let e2 = m[2] === '' ? st.size - 1 : Math.min(Number(m[2]), st.size - 1);
    if (isNaN(s) || s > e2 || s >= st.size) {
      res.writeHead(416, { 'content-range': 'bytes */' + st.size });
      return res.end();
    }
    base['content-range'] = 'bytes ' + s + '-' + e2 + '/' + st.size;
    base['content-length'] = e2 - s + 1;
    res.writeHead(206, base);
    fs.createReadStream(fp, { start: s, end: e2 }).pipe(res);
    return;
  }
  base['content-length'] = st.size;
  res.writeHead(200, base);
  fs.createReadStream(fp).pipe(res);
}
function dlOpenFile(req, res, parsed) {
  /* 只允许电脑本机触发"打开"：手机上点开会打开电脑上的文件没有意义 */
  if (!/^(127\.0\.0\.1|localhost)(:\d+)?$/i.test(String(req.headers.host || ''))) {
    return res.writeHead(403).end('仅限本机操作');
  }
  const j = dlJobs.get(parsed.searchParams.get('id') || '');
  if (!j || j.status !== 'done' || !j.file) return res.writeHead(404).end('Not found');
  const fp = path.join(DL_DIR, j.file);
  if (!fs.existsSync(fp)) return res.writeHead(404).end('文件不存在');
  try {
    const { exec } = require('child_process');
    if (process.platform === 'win32') exec('start "" "' + fp + '"');
    else if (process.platform === 'darwin') exec('open "' + fp + '"');
    else exec('xdg-open "' + fp + '"');
    res.writeHead(204).end();
  } catch (e) {
    res.writeHead(500).end(String(e.message || e));
  }
}
function readJsonBody(req, res, cb) {
  let body = '';
  let over = false;
  req.on('data', (c) => {
    body += c;
    if (body.length > 65536) { over = true; req.destroy(); }
  });
  req.on('end', () => {
    if (over) return;
    let j = {};
    try { j = JSON.parse(body || '{}'); } catch (e) { /* ignore */ }
    cb(j);
  });
  req.on('error', () => res.end());
}
function handleDlStart(req, res) {
  readJsonBody(req, res, (b) => {
    const r = dlStart(String(b.url || ''), String(b.ref || ''), String(b.name || ''));
    res.writeHead(r.err ? 400 : 200, {
      'content-type': 'application/json; charset=utf-8',
      'access-control-allow-origin': '*',
      'cache-control': 'no-store',
    });
    res.end(JSON.stringify(r));
  });
}
function handleDlCtl(req, res) {
  readJsonBody(req, res, (b) => {
    const act = String(b.action || '');
    let r;
    if (act === 'pause') r = dlPause(b.id);
    else if (act === 'resume') r = dlResume(b.id);
    else if (act === 'remove') r = dlRemove(b.id, !!b.delFile);
    else if (act === 'clear') r = dlClearFinished();
    else r = { err: '未知操作' };
    res.writeHead(r.err ? 400 : 200, {
      'content-type': 'application/json; charset=utf-8',
      'access-control-allow-origin': '*',
      'cache-control': 'no-store',
    });
    res.end(JSON.stringify(r));
  });
}

/* ------------------------------------------------------------------ *
 * 媒体嗅探（视频 / 音频 / HLS）
 * 所有页面流量都经过代理，这里是最可靠的嗅探点：按响应 Content-Type
 * 与 URL 扩展名识别媒体资源并记录，供外壳"媒体"面板展示、播放与下载。
 * HLS/DASH 分片（.ts/.m4s）不单独记录，由 m3u8/mpd 播放列表统一代表。
 * ------------------------------------------------------------------ */
const MEDIA_MAX = 200;
const MEDIA_SKIP_EXT = /\.(ts|m4s|key)(?:[?#]|$)/i;
const mediaItems = []; // 最新在前
const mediaKeys = new Map(); // host+pathname -> item（签名 URL 每次都可能变，按路径去重）
let mediaSeq = 1;

function mediaExtOf(u) {
  const m = /\.([a-z0-9]{2,5})(?:[?#]|$)/i.exec(u.pathname);
  return m ? m[1].toLowerCase() : '';
}
function mediaKindOf(u, ctRaw) {
  const ct = String(ctRaw || '').toLowerCase();
  const ext = mediaExtOf(u);
  if (/mpegurl/.test(ct) || ext === 'm3u8') return 'hls';
  if (/dash\+xml/.test(ct) || ext === 'mpd') return 'dash';
  if (/^video\//.test(ct)) return 'video';
  if (/^audio\//.test(ct)) return 'audio';
  if (/^(mp3|m4a|aac|flac|ogg|opus|wav|wma|m4b)$/.test(ext)) return 'audio';
  if (/^(mp4|m4v|mov|webm|mkv|avi|flv|wmv|3gp|ogv)$/.test(ext)) return 'video';
  return '';
}
/* pageRef：发起该请求的真实页面地址，媒体下载时还原 Referer 用 */
function mediaPageRef(clientReq) {
  try {
    const xr = clientReq && clientReq.headers['x-nova-ref'];
    if (xr) return decodeURIComponent(xr);
  } catch (e) { /* ignore */ }
  try {
    const rf = clientReq && clientReq.headers.referer;
    if (rf) {
      const pu = new URL(rf, 'http://127.0.0.1');
      const q = pu.searchParams.get('__nova_url');
      if (q) return q;
      return pu.href;
    }
  } catch (e) { /* ignore */ }
  return '';
}
function mediaRecord(u, pres, clientReq) {
  try {
    const kind = mediaKindOf(u, pres.headers['content-type']);
    if (!kind) return;
    if (kind !== 'hls' && kind !== 'dash' && MEDIA_SKIP_EXT.test(u.pathname)) return;
    const key = u.host + u.pathname;
    const size = Number(pres.headers['content-length']) || 0;
    const exist = mediaKeys.get(key);
    if (exist) {
      exist.url = u.toString();
      exist.ts = Date.now();
      if (size) exist.size = size;
      return;
    }
    const it = {
      id: 'm' + mediaSeq++,
      url: u.toString(),
      host: u.hostname,
      kind,
      ext: mediaExtOf(u) || (kind === 'hls' ? 'm3u8' : kind === 'dash' ? 'mpd' : ''),
      mime: String(pres.headers['content-type'] || '').split(';')[0].trim(),
      size,
      ts: Date.now(),
      ref: mediaPageRef(clientReq),
    };
    it.key = key;
    mediaKeys.set(key, it);
    mediaItems.unshift(it);
    while (mediaItems.length > MEDIA_MAX) {
      const old = mediaItems.pop();
      mediaKeys.delete(old.key);
    }
  } catch (e) { /* ignore */ }
}
function handleMediaList(req, res, parsed) {
  const since = Number(parsed.searchParams.get('since') || 0);
  const items = since ? mediaItems.filter((x) => x.ts > since) : mediaItems;
  res.writeHead(200, {
    'content-type': 'application/json; charset=utf-8',
    'access-control-allow-origin': '*',
    'cache-control': 'no-store',
  });
  res.end(JSON.stringify({ items, now: Date.now() }));
}
function handleMediaClear(req, res) {
  mediaItems.length = 0;
  mediaKeys.clear();
  res.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'access-control-allow-origin': '*' });
  res.end(JSON.stringify({ ok: true }));
}

/* ------------------------------------------------------------------ *
 * HLS 播放代理：/__media/stream/<proto>/<host>/<path>?<query>
 * 路径里保留真实 host：m3u8 里的相对分片地址按本路径解析后天然指向
 * 同一路由（普通镜像路径 ?__nova_url= 参数在相对解析时会丢失）。
 * 播放列表中出现的绝对地址会被改写成本路由形式后返回。
 * ------------------------------------------------------------------ */
function mediaStreamHref(u) {
  return '/__media/stream/' + u.protocol.replace(':', '') + '/' + u.host + u.pathname + (u.search || '');
}
function mediaStreamTarget(parsed) {
  const rest = parsed.pathname.slice('/__media/stream/'.length);
  const s1 = rest.indexOf('/');
  if (s1 < 0) return null;
  const proto = rest.slice(0, s1) === 'https' ? 'https:' : 'http:';
  const rest2 = rest.slice(s1 + 1);
  const s2 = rest2.indexOf('/');
  if (s2 < 0) return null;
  const host = rest2.slice(0, s2);
  if (!/^[\w.-]+(:\d+)?$/.test(host)) return null;
  return proto + '//' + host + rest2.slice(s2) + (parsed.search || '');
}
function rewritePlaylist(text) {
  return String(text).replace(/https?:\/\/[^\s"'<>()\\]+/g, (m) => {
    try { return mediaStreamHref(new URL(m)); } catch (e) { return m; }
  });
}
function msFetch(res, realUrl, clientReq, depth) {
  let u;
  try { u = new URL(realUrl); } catch (e) { return sendErrorPage(res, 400, '媒体代理地址无效', ''); }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') return sendErrorPage(res, 400, '不支持的协议', '');
  if (PUBLIC_MODE && blockedTargetSync(u)) return sendErrorPage(res, 403, '该地址不可访问', '公网模式下不代理内网 / 保留网段地址。');
  const lib = u.protocol === 'https:' ? https : http;
  const headers = buildUpstreamHeaders(clientReq, u, null);
  headers.accept = '*/*';
  const preq = lib.request(
    {
      protocol: u.protocol, hostname: u.hostname, port: u.port || undefined,
      path: u.pathname + u.search, method: 'GET', headers, servername: u.hostname,
      lookup: PUBLIC_MODE ? safeLookup : undefined,
    },
    (pres) => {
      const code = pres.statusCode || 0;
      if ([301, 302, 303, 307, 308].includes(code) && pres.headers.location && depth < 6) {
        pres.resume();
        try { return msFetch(res, new URL(pres.headers.location, u).toString(), clientReq, depth + 1); }
        catch (e) { return sendErrorPage(res, 502, '跳转地址无效', ''); }
      }
      const ct = String(pres.headers['content-type'] || '');
      const out = {};
      for (const [k, v] of Object.entries(pres.headers)) {
        if (STRIP_HEADERS.has(k)) continue;
        out[k] = v;
      }
      out['access-control-allow-origin'] = '*';
      if (!(/mpegurl/i.test(ct) || /\.m3u8(?:[?#]|$)/i.test(u.pathname))) {
        /* 分片 / 媒体：原样透传（保留 Range 相关头） */
        res.writeHead(code || 200, out);
        pres.pipe(res);
        pres.on('error', () => res.end());
        return;
      }
      /* 播放列表：解压 -> 改写绝对地址 -> 输出 */
      delete out['content-encoding'];
      delete out['content-length'];
      const chunks = [];
      decodeBody(pres)
        .on('data', (c) => chunks.push(c))
        .on('error', () => { if (!res.headersSent) sendErrorPage(res, 502, '播放列表获取失败', ''); else res.end(); })
        .on('end', () => {
          try {
            const buf = Buffer.from(rewritePlaylist(Buffer.concat(chunks).toString('utf8')), 'utf8');
            out['content-type'] = 'application/vnd.apple.mpegurl';
            out['content-length'] = buf.length;
            out['cache-control'] = 'no-store';
            res.writeHead(200, out);
            res.end(buf);
          } catch (e) {
            if (!res.headersSent) sendErrorPage(res, 502, '播放列表处理失败', '');
            else res.end();
          }
        });
    }
  );
  preq.on('error', () => {
    if (!res.headersSent) sendErrorPage(res, 502, '媒体服务器连接失败', '');
    else res.end();
  });
  preq.setTimeout(30000, () => preq.destroy(new Error('媒体代理请求超时')));
  preq.end();
}
function handleMediaStream(req, res, parsed) {
  const target = mediaStreamTarget(parsed);
  if (!target) return sendErrorPage(res, 400, '媒体代理地址无效', '');
  return msFetch(res, target, req, 0);
}

function start(port) {
  const server = http.createServer((req, res) => {
    const parsed = new URL(req.url, 'http://127.0.0.1');
    const p = parsed.pathname;

    /* 公网模式：按来源 IP 限流（静态文件走 CDN/缓存，无需计数） */
    if (PUBLIC_MODE && !/\.(png|jpe?g|gif|svg|ico|webp|woff2?|ttf)$/i.test(p)) {
      if (rateLimited(clientIpOf(req))) {
        res.writeHead(429, { 'content-type': 'text/plain; charset=utf-8', 'retry-after': '60' });
        return res.end('请求过于频繁，请稍后再试（公网实例按 IP 限流）');
      }
    }

    /* 镜像路径代理：任何带 __nova_url 参数的请求都转发到真实地址 */
    const novaTarget = parsed.searchParams.get('__nova_url');
    if (novaTarget) {
      /* 顶层文档导航（浏览器直接打开/刷新带 __nova_url 的地址）时返回外壳本身：
       * 外壳启动时读取 __nova_url 在框架内重建会话。若照旧转发，顶层会变成
       * 没有外壳的裸站点页，注入脚本的 navigate 消息发给自身无人接收，
       * 表现为"点击链接/播放卡没有任何反应"。iframe 内的镜像加载是
       * Sec-Fetch-Dest: iframe，不受影响；无该请求头的客户端照旧转发。
       * 例外：带 _nova_p2v=1 标记的请求是"哔哩哔哩外链播放器→视频页"提升跳转，
       * 壳 iframe 会让 B 站视频页触发嵌入检测降级为卡页（立即播放死循环），
       * 这里直接放行为裸视频页（顶层全屏可播）。 */
      if (
        req.method === 'GET' &&
        String(req.headers['sec-fetch-dest'] || '') === 'document' &&
        !req.url.includes('_nova_p2v=1')
      ) {
        return serveStatic(req, res, 'index.html');
      }
      if (req.method === 'POST' || req.method === 'PUT' || req.method === 'PATCH') {
        const bufs = [];
        let size = 0;
        req.on('data', (c) => {
          size += c.length;
          if (size > 8 * 1024 * 1024) {
            req.destroy();
            return;
          }
          bufs.push(c);
        });
        req.on('end', () => proxyRequest(req, res, novaTarget, 0, req.method, Buffer.concat(bufs)));
        req.on('error', () => res.end());
        return;
      }
      return proxyRequest(req, res, novaTarget, 0, 'GET', null);
    }

    if (p === '/__health') {
      res.writeHead(200, {
        'content-type': 'application/json',
        'access-control-allow-origin': '*',
        'cache-control': 'no-store',
      });
      return res.end(JSON.stringify({ ok: true, port }));
    }

    if (p === '/__ck') return handleCookieSync(req, res, parsed);
    if (p === '/__log') return handlePageLog(req, res, parsed);

    /* 媒体嗅探：列表 / 清空 / HLS 播放代理 */
    if (p === '/__media/list') return handleMediaList(req, res, parsed);
    if (p === '/__media/clear' && req.method === 'POST') return handleMediaClear(req, res);
    if (p.startsWith('/__media/stream/')) return handleMediaStream(req, res, parsed);

    /* 下载管理器接口 */
    if (p === '/__dl/list') {
      res.writeHead(200, {
        'content-type': 'application/json; charset=utf-8',
        'access-control-allow-origin': '*',
        'cache-control': 'no-store',
      });
      let hasActive = false;
      dlJobs.forEach((j) => { if (j.status === 'downloading') hasActive = true; });
      return res.end(JSON.stringify({ ok: true, hasActive, jobs: dlList() }));
    }
    if (p === '/__dl/start' && req.method === 'POST') return handleDlStart(req, res);
    if (p === '/__dl/ctl' && req.method === 'POST') return handleDlCtl(req, res);
    if (p === '/__dl/file') return dlServeFile(req, res, parsed);
    if (p === '/__dl/open') return dlOpenFile(req, res, parsed);

    if (p === '/__fav') {
      const t = parsed.searchParams.get('u');
      if (!t) return res.writeHead(400).end();
      return proxyFavicon(t, res);
    }

    if (p === '/__p') {
      const t = parsed.searchParams.get('url');
      if (!t) return sendErrorPage(res, 400, '缺少目标地址', '代理请求未携带 <code>url</code> 参数。');
      if (req.method === 'POST' || req.method === 'PUT' || req.method === 'PATCH') {
        const bufs = [];
        let size = 0;
        req.on('data', (c) => {
          size += c.length;
          if (size > 8 * 1024 * 1024) {
            req.destroy();
            return;
          }
          bufs.push(c);
        });
        req.on('end', () => proxyRequest(req, res, t, 0, req.method, Buffer.concat(bufs)));
        req.on('error', () => res.end());
        return;
      }
      return proxyRequest(req, res, t, 0, 'GET', null);
    }

    /* 兜底中转：页面里未被钩住的跳转（如 location.href='/xxx'）会打到本站裸路径。
     * 优先从 Referer 还原目标站点；Referer 缺失（站点 no-referrer 策略/重定向链）
     * 时退回到该客户端最近一次代理的站点 origin。 */
    if (p !== '/' && p !== '/index.html' && !p.startsWith('/__')) {
      let rOrigin = null;
      const rf = req.headers['referer'];
      if (rf) {
        try {
          const ru = new URL(rf);
          const rt = ru.searchParams.get('__nova_url');
          if (rt) rOrigin = new URL(unwrapSelf(req.headers.host || '', rt)).origin;
        } catch (e) { /* ignore */ }
      }
      if (!rOrigin) {
        const rec = LAST_ORIGIN.get(clientIpOf(req));
        if (rec && Date.now() - rec.t < LAST_ORIGIN_TTL) rOrigin = rec.origin;
      }
      if (rOrigin) {
        res.writeHead(302, { location: p + parsed.search + (parsed.search ? '&' : '?') + '__nova_url=' + encodeURIComponent(rOrigin + p + parsed.search) });
        return res.end();
      }
    }

    if (p === '/' || p === '/index.html') return serveStatic(req, res, 'index.html');
    if (/^\/(?!__)[\w.-]+$/.test(p)) return serveStatic(req, res, p.slice(1));
    res.writeHead(404).end('Not found');
  });

  server.on('error', (err) => {
    /* 云平台用 PORT 指定端口，必须严格监听该端口（顺延会导致健康检查失败） */
    if (err.code === 'EADDRINUSE' && !process.env.PORT && port < BASE_PORT + 20) {
      start(port + 1);
    } else {
      console.error('服务启动失败:', err.message);
      process.exit(1);
    }
  });

  server.listen(port, '0.0.0.0', () => {
    const os = require('os');
    const ips = [];
    Object.keys(os.networkInterfaces()).forEach(k => {
      (os.networkInterfaces()[k] || []).forEach(n => {
        if (n.family === 'IPv4' && !n.internal) ips.push(n.address);
      });
    });
    console.log('');
    if (PUBLIC_MODE) {
      console.log('  Nova Browser 已启动（公网模式）');
      console.log('  监听端口:   ' + port + '（来自 PORT 环境变量）');
      console.log('  安全护栏:   已启用 —— 拒绝内网/元数据地址、按 IP 限流 ' + RATE_MAX + ' 次/分钟');
    } else {
      console.log('  Nova Browser 已启动（局域网可访问）');
    }
    console.log('  本机访问:   http://127.0.0.1:' + port);
    ips.forEach(ip => {
      console.log('  局域网访问: http://' + ip + ':' + port + '   <- 手机连同一 WiFi 可打开');
    });
    console.log('  提示: 手机打不开时，检查 Windows 防火墙是否放行 Node.js / 该端口');
    console.log('  停止服务:  Ctrl + C');
    console.log('');
  });
}

dlLoad();
start(BASE_PORT);
