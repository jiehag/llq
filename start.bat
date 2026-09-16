@echo off
chcp 65001 >nul
title Nova Browser
cd /d "%~dp0"

set NODE="%USERPROFILE%\.workbuddy\binaries\node\versions\22.22.2-3\node.exe"
if not exist %NODE% set NODE=node

echo.
echo   Nova Browser - 正在启动本地渲染代理服务...
echo.

start "" http://127.0.0.1:7180
%NODE% server.js

pause
