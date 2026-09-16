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
function parseSetCookie(raw) {
  const parts = String(raw).split(';');
  const eq = parts[0].indexOf('=');
  if (eq <= 0) return null;
  const name = parts[0].slice(0, eq).trim();
  const value = parts[0].slice(eq + 1).trim();
  if (!name) return null;
  let dead = false;
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
  }
  return dead ? { name, dead: true } : { name, value, dead: false };
}
function storeCookies(host, list) {
  if (!list) return;
  const items = Array.isArray(list) ? list : [list];
  const j = jarOf(baseDomainOf(host));
  for (const raw of items) {
    const c = parseSetCookie(raw);
    if (!c) continue;
    if (c.dead) j.delete(c.name);
    else j.set(c.name, c.value);
  }
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
    'var P=window.parent;',
    'function post(m){try{m.__nova=1;P.postMessage(m,"*");}catch(e){}}',
    /* 原生函数伪装：被包装的函数 toString 时返回原生签名。
     * 阿里系风控脚本（um.js 等）会检查 Function.prototype.toString 判断
     * 原生函数是否被篡改，检测到就提高验证码挑战频率。 */
    'function __nat(f,orig){try{var s=Function.prototype.toString.call(orig);',
    '  Object.defineProperty(f,"toString",{value:function(){return s;},configurable:true,writable:true});}catch(e){}return f;}',

    /* ---------- 反调试中和 ----------
     * 很多站用 Function("debugger")/eval("debugger")/setInterval 循环做反调试，
     * 开发者工具一旦打开（或打开过）页面就反复暂停（"已在调试程序中暂停"）。
     * 这里在页面脚本运行前把 debugger 语句剥掉：仅当检测到 debugger 时才介入，不影响正常代码。 */
    'try{',
    '  var _NF=window.Function;',
    '  function stripDbg(s){return String(s).replace(/\\bdebugger\\b/g,"");}',
    '  var NF=function(){',
    '    var a=[].slice.call(arguments);',
    '    var body=a[a.length-1];',
    '    if(typeof body==="string"&&body.indexOf("debugger")>=0){',
    '      for(var i=0;i<a.length;i++){if(typeof a[i]==="string")a[i]=stripDbg(a[i]);}',
    '    }',
    '    return _NF.apply(this,a);',
    '  };',
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
    'function ckPost(v){ckQ.push(v);if(ckTimer)return;ckTimer=setTimeout(ckFlush,250);}',
    'function ckFlush(){ckTimer=null;var b=ckQ.join("\\n");ckQ=[];',
    '  try{fetch(PROXY+"/__ck?o="+encodeURIComponent(RU)+"&t="+encodeURIComponent(CKT),{method:"POST",body:b,keepalive:true});}catch(e){}}',
    /* 关键：验证码组件（阿里 x5sec 等）成功后写 Cookie 会立刻 reload 页面，
     * 250ms 批量定时器被打断会导致验证通过的 Cookie 永远不上报、验证码反复出现。
     * 页面卸载/隐藏时立即同步冲刷（fetch keepalive 保证卸载后仍能送达）。 */
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
    '    get:function(){return ckSerialize();},',
    '    set:function(v){ckApply(v);ckPost(v);}});',
    '}catch(e){}',

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
    '      if(x.__nOrig){try{Object.defineProperty(x,"responseURL",{get:function(){return x.__nOrig;},configurable:true});}catch(e){}}',
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

    /* ---------- 动态 iframe 重写 ---------- */
    'function fixFrame(el){',
    '  try{',
    '    if(!el||el.tagName!=="IFRAME")return;',
    '    var s=el.getAttribute("src");',
    '    if(!s)return;',
    '    if(/^(about|javascript|data|blob):/i.test(s))return;',
    '    var abs=new URL(s,realHref()).href;',
    '    if(!/^https?:/i.test(abs))return;',
    '    if(abs.indexOf(PROXY)===0)return;',
    '    var p=PROXY+ppath(abs);',
    '    if(el.src!==p)el.src=p;',
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
    '            if(n.tagName==="IFRAME")fixFrame(n);',
    '            if(n.querySelectorAll){var l=n.querySelectorAll("iframe[src]");for(var k2=0;k2<l.length;k2++)fixFrame(l[k2]);}',
    '          }',
    '        }',
    '      }',
    '    }',
    '  });',
    '  mo.observe(document.documentElement||document,{childList:true,subtree:true,attributes:true,attributeFilter:["src"]});',
    '}catch(e){}',

    /* ---------- 导航劫持 ---------- */
    'function abs(u){try{return new URL(u,realHref()).href;}catch(e){return String(u);}}',
    'function findA(n){while(n&&n.nodeType===1&&n.tagName!=="A")n=n.parentElement;return n&&n.tagName==="A"?n:null;}',
    /* 用 window 捕获 + stopImmediatePropagation：百度/必应等站点在 document 上也挂了
     * 点击处理器（会额外调用 window.open 造成重复开标签），stopPropagation 挡不住
     * 同节点上的其他监听器，必须用 stopImmediatePropagation 才能完全接管一次点击。 */
    'window.addEventListener("click",function(e){',
    '  var a=findA(e.target);if(!a)return;',
    '  var raw=a.getAttribute("href");',
    '  if(!raw||raw.charAt(0)==="#")return;',
    '  if(/^(javascript|mailto|tel|data|blob|about):/i.test(raw))return;',
    '  if(a.hasAttribute("download"))return;',
    '  e.preventDefault();e.stopImmediatePropagation();',
    '  post({type:"navigate",url:abs(raw),newTab:(a.target==="_blank"||e.ctrlKey||e.metaKey||e.shiftKey)});',
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
  try { u.searchParams.delete('__nova_url'); } catch (e) { /* ignore */ }
  const s = u.search;
  return u.pathname + s + (s ? '&' : '?') + '__nova_url=' + encodeURIComponent(u.href);
}

function rewriteIframeSrcs(html, realUrl) {
  return html.replace(
    /<iframe\b([^>]*?)\bsrc\s*=\s*(["'])([^"']+)\2/gi,
    (m, pre, q, src) => {
      const t = src.trim();
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

function rewriteHtml(html, realUrl) {
  // 1) 干掉页面内的 CSP / content-type meta
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
    if (lk.startsWith('sec-') || lk.startsWith('proxy-')) continue;
    headers[lk] = v;
  }

  headers['user-agent'] = (clientReq.headers['user-agent'] || UA).replace(/HeadlessChrome/gi, 'Chrome');
  headers['accept'] =
    clientReq.headers['accept'] ||
    'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8';
  headers['accept-language'] = clientReq.headers['accept-language'] || 'zh-CN,zh;q=0.9,en;q=0.8';
  headers['accept-encoding'] = 'gzip, deflate, br';

  /* Referer / Origin 还原为真实站点，兼容防盗链与 CSRF 校验 */
  let realRef = null;
  const ref = clientReq.headers['referer'];
  if (ref) {
    try {
      const ru = new URL(ref);
      const nt = ru.searchParams.get('__nova_url');
      if (nt) {
        realRef = unwrapSelf(req.headers.host || '', nt);
      } else if (ru.pathname === '/__p') {
        const target = ru.searchParams.get('url');
        if (target) realRef = target;
      } else if (/^https?:/i.test(ref)) {
        realRef = ref;
      }
    } catch (e) { /* ignore */ }
  }
  if (realRef) {
    headers['referer'] = realRef;
    try { headers['origin'] = new URL(realRef).origin; } catch (e) { /* ignore */ }
  } else {
    headers['referer'] = u.origin + '/';
    if ((clientReq.method || 'GET') !== 'GET') headers['origin'] = u.origin;
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

  const lib = u.protocol === 'https:' ? https : http;
  const headers = buildUpstreamHeaders(clientReq, u, bodyBuf);

  const preq = lib.request(
    {
      protocol: u.protocol,
      hostname: u.hostname,
      port: u.port || undefined,
      path: u.pathname + u.search,
      method: method || 'GET',
      headers,
      servername: u.hostname,
    },
    (pres) => {
      const code = pres.statusCode || 200;
      if ([301, 302, 303, 307, 308].includes(code) && pres.headers.location && depth < 8) {
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
      return handleUpstream(pres, clientRes, u);
    }
  );

  preq.on('error', (err) => {
    if (!clientRes.headersSent) {
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

function handleUpstream(pres, res, u) {
  storeCookies(u.hostname, pres.headers['set-cookie']);

  const ct = String(pres.headers['content-type'] || '').toLowerCase();
  const isHtml = ct.includes('text/html') || ct.includes('application/xhtml+xml');

  const out = {};
  for (const [k, v] of Object.entries(pres.headers)) {
    if (STRIP_HEADERS.has(k)) continue;
    out[k] = v;
  }
  out['access-control-allow-origin'] = '*';
  out['access-control-allow-headers'] = '*';
  out['access-control-allow-methods'] = 'GET,POST,PUT,DELETE,OPTIONS,PATCH';
  out['access-control-expose-headers'] = '*';

  if (!isHtml) {
    // 二进制 / 流媒体：原样透传，保留 Range 相关头，视频进度可拖动
    if (!out['cache-control']) out['cache-control'] = 'public, max-age=300';
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
    res.writeHead(200, {
      'content-type': MIME[path.extname(full).toLowerCase()] || 'application/octet-stream',
      'cache-control': 'no-cache',
    });
    res.end(data);
  });
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
        const j = jarOf(baseDomainOf(host));
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

function start(port) {
  const server = http.createServer((req, res) => {
    const parsed = new URL(req.url, 'http://127.0.0.1');
    const p = parsed.pathname;

    /* 镜像路径代理：任何带 __nova_url 参数的请求都转发到真实地址 */
    const novaTarget = parsed.searchParams.get('__nova_url');
    if (novaTarget) {
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
     * 若 Referer 是镜像代理页，则 302 到对应的镜像 URL，保证导航不断链。 */
    if (p !== '/' && p !== '/index.html' && !p.startsWith('/__')) {
      const rf = req.headers['referer'];
      if (rf) {
        try {
          const ru = new URL(rf);
          const rt = ru.searchParams.get('__nova_url');
          if (rt) {
            const rOrigin = new URL(unwrapSelf(req.headers.host || '', rt)).origin;
            res.writeHead(302, { location: p + parsed.search + (parsed.search ? '&' : '?') + '__nova_url=' + encodeURIComponent(rOrigin + p + parsed.search) });
            return res.end();
          }
        } catch (e) { /* ignore */ }
      }
    }

    if (p === '/' || p === '/index.html') return serveStatic(req, res, 'index.html');
    if (/^\/(?!__)[\w.-]+$/.test(p)) return serveStatic(req, res, p.slice(1));
    res.writeHead(404).end('Not found');
  });

  server.on('error', (err) => {
    if (err.code === 'EADDRINUSE' && port < BASE_PORT + 20) {
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
    console.log('  Nova Browser 已启动（局域网可访问）');
    console.log('  本机访问:   http://127.0.0.1:' + port);
    ips.forEach(ip => {
      console.log('  局域网访问: http://' + ip + ':' + port + '   <- 手机连同一 WiFi 可打开');
    });
    console.log('  提示: 手机打不开时，检查 Windows 防火墙是否放行 Node.js / 该端口');
    console.log('  停止服务:  Ctrl + C');
    console.log('');
  });
}

start(BASE_PORT);
