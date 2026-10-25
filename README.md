# wanxiang-game · 最強王者萬象版 后端

万象版本，重构整套回合时序与结算引擎，删档测试，非商用测试项目。

《最強王者萬象版》离线版游戏后端：Python 标准库 `http.server` 实现的
Flash Remoting（AMF0/AMF3）服务器，账号存放在 Turso（libSQL）。

## 目录

```
server/
  game_server.py      # 主服务：AMF 网关 / 公告页 / 注册登录 HTTP 接口
  amf.py              # AMF0 / AMF3 编解码
  avatar_catalog.py   # 英雄/怪物/建筑/材料图鉴
  equip_catalog.py    # 装备图鉴
  hero_data.py        # 英雄名称/技能/召唤物数据
  hero_taxonomy.py    # 英雄定位/属性
requirements.txt
render.yaml           # Render Blueprint（可选，一键部署）
```

## 本地运行

```bash
pip install -r requirements.txt
# 在 server/.env 里配置（该文件已被 .gitignore 排除，切勿提交）：
#   TURSO_DATABASE_URL=libsql://...
#   TURSO_AUTH_TOKEN=...
python server/game_server.py
```

默认监听 `0.0.0.0:8080`（可用 `PORT` 环境变量覆盖）。

## 部署到 Render

### 方式 A：Blueprint（推荐）

1. Render 控制台 → **New → Blueprint**
2. 选择本仓库 → Render 会读取 `render.yaml`
3. 按提示填写两个 Secret：
   - `TURSO_DATABASE_URL`（形如 `libsql://xxx.turso.io`）
   - `TURSO_AUTH_TOKEN`
4. 点 **Deploy**

### 方式 B：手动创建 Web Service

1. **New → Web Service** → 连接本仓库
2. Language: **Python**；Branch: `main`
3. Build Command: `pip install -r requirements.txt`
4. Start Command: `python server/game_server.py`
5. Instance Type: **Free**（免费实例 15 分钟无请求会休眠，冷启动约 30-60 秒）
6. Environment Variables：
   | Key | Value |
   | --- | --- |
   | `TURSO_DATABASE_URL` | `libsql://...`（Turso 控制台 → Database → URL） |
   | `TURSO_AUTH_TOKEN` | Turso 控制台 → Create Token / 现有 token |
   | `PYTHON_VERSION` | `3.12.7` |
7. **Create Web Service**

部署完成后服务地址形如 `https://<name>.onrender.com`。

## 接口

| 方法 | 路径 | 说明 |
| --- | --- | --- |
| POST | `/x/gateway/?v=9.1.0` | AMF 网关（客户端主通道） |
| GET | `/x/notice/?v=9.1.0` | 游戏公告 HTML |
| GET | `/x/help/<page>.html` | 帮助/开发者/公告页 |
| POST | `/register` | JSON 注册 `{"account","password"}` |
| POST | `/login` | JSON 登录 |
| GET | `/` | 健康检查，返回 `ok` |

## 客户端接入

桌面客户端在 `MainConfig.as` 的 `$isDebug` 分支里写死了服务地址
（`http://127.0.0.1:8080/x`），上线前需要改成
`https://<name>.onrender.com/x` 并重新编译 `MainLLOL.swf`。

## 安全

- `server/.env`、`server/server_log.txt`、账号备份 JSON 均不进入仓库。
- 数据库 token 只放在 Render 的 Environment Variables 里，不要写进代码或提交。
