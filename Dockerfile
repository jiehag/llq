# Nova Browser —— 渲染代理服务
# 零依赖，仅需 Node 运行时。云平台会注入 PORT 环境变量，server.js 自动进入公网模式。
FROM node:20-alpine

WORKDIR /app

# 项目零第三方依赖，无需 npm install
COPY . .

ENV NODE_ENV=production \
    NOVA_PUBLIC=1

EXPOSE 7180

# 健康检查：/__health 返回 {"ok":true}
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
  CMD node -e "require('http').get({host:'127.0.0.1',port:process.env.PORT||7180,path:'/__health'},r=>process.exit(r.statusCode===200?0:1)).on('error',()=>process.exit(1))"

CMD ["node", "server.js"]
