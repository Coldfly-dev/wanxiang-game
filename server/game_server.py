# -*- coding: utf-8 -*-
"""Local Flash Remoting (AMF) server for the dead meng52 "最强王者 / LOL" game.

The client (assets/MainLLOL.swf) talks Flash Remoting to
    http://<host>/gateway/?v=<version>
using service name "http_api".  Every call carries a plain object:
    { method: "user.llogin", params: {actionID: "...", ...}, uid, sessionid,
      app_version, cfg_version }
and expects back:
    { method, params, return_code: 0, data: {...}, server_now: <Date> }
"""
import copy
import datetime
import json
import os
import random
import re
import struct
import sys
import threading
import time
import traceback
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amf import Reader, read_amf0, encode_amf0, encode_amf3, enc_str  # noqa: E402

# 2026-10-25: Turso (libSQL) persistence + password hashing.  Both packages
# are listed in requirements.txt; the server refuses to start without them.
try:
    import bcrypt
except ImportError:                                     # pragma: no cover
    bcrypt = None
try:
    from libsql_client import create_client_sync
except ImportError:                                     # pragma: no cover
    create_client_sync = None

try:                                # generated from the client's icon atlases
    from equip_catalog import EQUIP_CATALOG
except ImportError:                 # pragma: no cover
    EQUIP_CATALOG = {}

try:                                # every hero icon in hero_A..D atlases
    from avatar_catalog import AVATAR_CATALOG
except ImportError:                 # pragma: no cover
    AVATAR_CATALOG = {}

try:                                # reconstructed names + skill kits
    from hero_data import (HERO_NAMES, UNIT_NAMES, HERO_SKILLS,
                           GENERIC_SKILLS, SKIN_BASE, PASSIVE_SKILLS,
                           SUMMON_AVATARS, UNIT_CATEGORIES,
                           SUMMON_SKILLS, SUMMON_DEFAULT_SKILL,
                           SUMMON_FAMILIES, SKILL_DIFF,
                           EXP_MATERIAL_FAMILIES, GALLERY_HIDDEN,
                           GALLERY_SORT_OVERRIDES, ARCH_OVERRIDES,
                           ACTION_OVERRIDES, RANGE_OVERRIDES,
                           EFFECT_OVERRIDES, TACTIC_BY_FAMILY)
except ImportError:                 # pragma: no cover
    HERO_NAMES, UNIT_NAMES, HERO_SKILLS = {}, {}, {}
    GENERIC_SKILLS, SKIN_BASE = {}, {}
    PASSIVE_SKILLS, SUMMON_AVATARS = {}, {}
    SUMMON_SKILLS, SUMMON_DEFAULT_SKILL, SUMMON_FAMILIES = {}, None, set()
    SKILL_DIFF = {}
    UNIT_CATEGORIES, EXP_MATERIAL_FAMILIES = {}, set()
    GALLERY_HIDDEN, GALLERY_SORT_OVERRIDES = set(), {}
    ARCH_OVERRIDES = {}
    ACTION_OVERRIDES = {}
    RANGE_OVERRIDES = {}
    EFFECT_OVERRIDES = {}
    TACTIC_BY_FAMILY = {}

# 2026-10-23: per-family damage-type overrides (1 physical / 2 magic /
# 3 true).  A_1079 費德提克 is gallery #50 but HERO_INDEX lists it 49,
# which classified him as physical; the user wants magic damage.
DAMAGE_TYPE_OVERRIDES = {"A_1079": 2}

try:                                # three-tier 5-star hero stat templates
    from hero_taxonomy import hero_stats, HERO_INDEX, TIER_BY_INDEX
except ImportError:                 # pragma: no cover
    hero_stats = None
    HERO_INDEX = {}
    TIER_BY_INDEX = {}

# Merge summon-only monster families into the generated catalog.  They use
# existing icon ids (``res``) so no new SWF asset is needed.
AVATAR_CATALOG.update(SUMMON_AVATARS)

# 2026-10-21 hero 7★ tier: 6★3阶 -> 7★ is the final star-up.  The client has
# no 7★ art, so the 7★ entry reuses the 6★ `res` (standing art + card icon).
for _aid7, _meta7 in list(AVATAR_CATALOG.items()):
    if not _aid7.endswith("_6"):
        continue
    try:
        if int(_meta7.get("kind", 1)) != 1:
            continue
    except (TypeError, ValueError):
        continue
    _base7 = _aid7[:-2]
    _new7 = dict(_meta7)
    _new7["star"] = 7
    _new7["res"] = _aid7
    _new7["next"] = ""
    AVATAR_CATALOG[_base7 + "_7"] = _new7

# 2026-10-21 equipment secondary-stat redefinition.
#   crit / tough are stored in 0.1% units; critdmg is stored in percent.
# Each equipment type has two fixed inherent secondary attributes.  The
# values themselves are seeded per star in _ensure_equips below; this map
# only controls which two attributes EquipData.hasAttr() exposes.
_EQUIP_ATTR_PAIR = {
    "1": ("crit", "critdmg"),   # weapon
    "3": ("tough", "hit"),      # armor
    "4": ("crit", "critdmg"),   # accessory
    "5": ("flee", "hit"),       # boots
    "6": ("crit", "critdmg"),   # skill book
}
for _eq_meta in EQUIP_CATALOG.values():
    _eq_typ = str(_eq_meta.get("type", ""))
    _eq_pl = _eq_meta.get("pl")
    if _eq_typ in _EQUIP_ATTR_PAIR and isinstance(_eq_pl, list) and len(_eq_pl) >= 8:
        _eq_pl[6], _eq_pl[7] = _EQUIP_ATTR_PAIR[_eq_typ]

# 2026-10-21 endgame unification: five skill-book templates only ship 5★
# art.  Synthesize 7★ catalog rows that reuse the 5★ icon, so every
# remaining book can become 7★ (red frame) without missing textures.
for _book_base in ("E_6009", "E_6010", "E_6201", "E_6505", "E_6506"):
    _book_src = EQUIP_CATALOG.get(_book_base + "_5")
    if not _book_src:
        continue
    _book_dst = dict(_book_src)
    _book_pl = list(_book_src.get("pl") or [])
    for _bi in range(min(4, len(_book_pl))):
        _book_pl[_bi] = int(round(float(_book_pl[_bi]) * 1.4))
    _book_dst["pl"] = _book_pl
    _book_dst["gold"] = 700
    _book_dst["res"] = _book_src.get("res", "EQ_%s_5" % _book_base.split("_")[1])
    EQUIP_CATALOG[_book_base + "_7"] = _book_dst

# A handful of event/special gear templates likewise stop at 5★.  Clone
# them into 6★ rows (5★ icon, ~1.2x primary stats) so the whole surviving
# inventory can be unified to orange 6★.
for _gear_base in ("E_1004", "E_1005", "E_1014", "E_1015", "E_1499",
                   "E_1501", "E_1502", "E_1503", "E_1999", "E_3999",
                   "E_4001", "E_4003", "E_4004", "E_5001", "E_5003",
                   "E_5004", "E_5999"):
    _gear_src = EQUIP_CATALOG.get(_gear_base + "_5")
    if not _gear_src:
        continue
    _gear_dst = dict(_gear_src)
    _gear_pl = list(_gear_src.get("pl") or [])
    for _gi in range(min(4, len(_gear_pl))):
        _gear_pl[_gi] = int(round(float(_gear_pl[_gi]) * 1.2))
    _gear_dst["pl"] = _gear_pl
    _gear_dst["gold"] = 600
    _gear_dst["res"] = _gear_src.get("res", "EQ_%s_5" % _gear_base.split("_")[1])
    EQUIP_CATALOG[_gear_base + "_6"] = _gear_dst

# 2026-10-21 equipment main-stat / affix redesign.
# pl[0..3] now store the MAX-level values (level 150); the client scales them
# linearly with the equipment level.  Dual main stats use half of each value.
# 2026-10-25 transitional balance: gear main stats HP/ATK x0.35, defences
# x0.20.  Only the hit/flee affixes are halved (base and wash weights
# together, so the forge/wash split is unchanged); crit / critdmg / tough
# keep their original values (user request).
_EQUIP_MAIN_MAX = {"hp": 11900, "ap": 8400, "d10": 8800, "d20": 8400}
_EQUIP_AFFIX_MAX = {"hit": 2500, "flee": 2400, "crit": 480,
                    "critdmg": 50, "tough": 260}
_EQUIP_WASH_MAX = {"hit": 1250, "flee": 1100, "crit": 220,
                   "critdmg": 25, "tough": 140}
_EQUIP_WASH_CLICKS = 255

# 2026-10-22 per-item overrides (user request):
#   E_1001 鑌鐵之鋒: main stat becomes ATK-only (generic weapon row gave HP).
#   E_4023 無羈之鍪: affixes become hit + crit resistance (was flee + tough).
_EQUIP_MAIN_OVERRIDES = {"E_1001": ("ap",)}
_EQUIP_AFFIX_OVERRIDES = {"E_4023": ("hit", "tough"),
                          "E_3010": ("flee", "tough")}

# 2026-10-23 weapon roles (user design).  Template numbers are the middle
# segment of E_<tpl>_<star>.
#   輸出: main ATK only, affixes crit rate + crit damage.
#   戰士: main ATK + HP, affixes hit/flee (alternating) + crit resistance.
#   坦克: main HP (some HP+one defence), affixes hit + crit resistance.
WEAPON_DPS = {
    "1001", "1002", "1004", "1005", "1011", "1012", "1013", "1014",
    "1015", "1019", "1020", "1021", "1024", "1025", "1027", "1029",
    "1030", "1033", "1041",
}
WEAPON_TANK = {
    "1018", "1022", "1026", "1028", "1031", "1032", "1052", "1053",
    "1501", "1502", "1503", "1504", "1505",
}
WEAPON_WARRIOR = {
    "1003", "1006", "1016", "1017", "1023", "1051", "1061", "1499",
    "1999",
}
# 坦克主屬性: 純生命; HP+物防; HP+法防.
TANK_MAIN_HP_D10 = {"1053", "1503", "1504"}
TANK_MAIN_HP_D20 = {"1052", "1502", "1505"}
# 戰士副屬性「命中/閃避」交替（按模板號排序）。
_WEAPON_WARRIOR_HIT = {
    tpl: (idx % 2 == 0)
    for idx, tpl in enumerate(sorted(WEAPON_WARRIOR))
}


def _apply_endgame_equip_stats():
    """Rewrite every endgame gear/book template to the fixed main-stat and
    affix rules.

    Weapons cycle HP / ATK / HP+ATK; armour cycles the three 2-of-3
    HP/PDEF/MDEF combinations; boots cycle HP+PDEF / HP+MDEF; accessories are
    HP-only.  Skill books have no main stats and no affixes (user decision).
    Only one item in the whole set carries the crit+critdmg pair: weapons.
    """
    groups = {"1": [], "3": [], "4": [], "5": [], "6": []}
    for _eid, _meta in EQUIP_CATALOG.items():
        _p = _eid.split("_")
        if len(_p) != 3 or len(_p[2]) != 1 or not _p[2].isdigit():
            continue
        _typ = str(_meta.get("type", ""))
        if _typ not in groups:
            continue
        if _typ == "6" and _p[2] != "7":
            continue
        if _typ != "6" and _p[2] != "6":
            continue
        groups[_typ].append((_p[1], _eid, _meta))
    for _typ, _rows in groups.items():
        _rows.sort()
        for _idx, (_tpl, _eid, _meta) in enumerate(_rows):
            _pl = list(_meta.get("pl") or [0] * 10)
            while len(_pl) < 10:
                _pl.append(0)
            _pl[0] = _pl[1] = _pl[2] = _pl[3] = 0
            if _typ == "1":
                if _tpl in WEAPON_TANK:
                    if _tpl in TANK_MAIN_HP_D10:
                        _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                        _pl[2] = _EQUIP_MAIN_MAX["d10"] // 2
                    elif _tpl in TANK_MAIN_HP_D20:
                        _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                        _pl[3] = _EQUIP_MAIN_MAX["d20"] // 2
                    else:
                        _pl[0] = _EQUIP_MAIN_MAX["hp"]
                    _pair = ("hit", "tough")
                elif _tpl in WEAPON_WARRIOR:
                    _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                    _pl[1] = _EQUIP_MAIN_MAX["ap"] // 2
                    _pair = (("hit" if _WEAPON_WARRIOR_HIT.get(_tpl, True)
                              else "flee"), "tough")
                else:
                    # 輸出武器（未列出的特殊武器也按輸出處理）。
                    _pl[1] = _EQUIP_MAIN_MAX["ap"]
                    _pair = ("crit", "critdmg")
            elif _typ == "3":
                _mode = _idx % 3
                if _mode == 0:
                    _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                    _pl[2] = _EQUIP_MAIN_MAX["d10"] // 2
                elif _mode == 1:
                    _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                    _pl[3] = _EQUIP_MAIN_MAX["d20"] // 2
                else:
                    _pl[2] = _EQUIP_MAIN_MAX["d10"] // 2
                    _pl[3] = _EQUIP_MAIN_MAX["d20"] // 2
                _pair = ("hit", "tough")
            elif _typ == "4":
                _pl[0] = _EQUIP_MAIN_MAX["hp"]
                _pair = (("hit", "tough") if _idx % 2 == 0
                         else ("flee", "tough"))
            elif _typ == "5":
                _mode = _idx % 2
                _pl[0] = _EQUIP_MAIN_MAX["hp"] // 2
                if _mode == 0:
                    _pl[2] = _EQUIP_MAIN_MAX["d10"] // 2
                else:
                    _pl[3] = _EQUIP_MAIN_MAX["d20"] // 2
                _pair = ("flee", "tough")
            else:                       # skill book
                _pair = ("", "")
            _pl[6], _pl[7] = _pair
            _base_id = "E_" + _tpl
            if _base_id in _EQUIP_MAIN_OVERRIDES:
                _pl[0] = _pl[1] = _pl[2] = _pl[3] = 0
                for _stat in _EQUIP_MAIN_OVERRIDES[_base_id]:
                    _pl[{"hp": 0, "ap": 1, "d10": 2, "d20": 3}[_stat]] = \
                        _EQUIP_MAIN_MAX[_stat]
            if _base_id in _EQUIP_AFFIX_OVERRIDES:
                _pl[6], _pl[7] = _EQUIP_AFFIX_OVERRIDES[_base_id]
            _meta["pl"] = _pl


_apply_endgame_equip_stats()

# Named endgame equipment.  The client catalog has no original names, so
# these three Mordekaiser-exclusive pieces get proper names here.
EQUIP_NAME_OVERRIDES = {
    "E_1032": "鐵獄的詛咒",
    "E_3009": "冥凱的緘言",
    "E_5009": "寂途的履聲",
    # 2026-10-22 Iron Man Teemo bond set.
    "E_1001": "鑌鐵之鋒",
    "E_4023": "無羈之鍪",
    "E_5007": "堅定之靴",
    "E_6505": "神技：天火",
    "E_6009": "神技：地獄星",
    "E_6201": "魔技：惡魔契約",
    # 2026-10-22 聯盟之喙艾尼維亞 bond set + book.
    "E_1501": "原初聖盾",
    "E_3007": "冥霜之翼",
    "E_4004": "干擾水晶",
    "E_6001": "狂暴復甦",
    # 2026-10-23 費德提克 bond set.
    "E_1030": "生鏽的鐮刀",
    "E_3010": "殘破的布袍",
    "E_4003": "昏黃的油燈",
    # 2026-10-24 毒系三人組 bond sets (伊莉絲/兔寶寶提莫/圖奇).
    # 伊莉絲：藍晶匕首、紫袍、紅花吊飾。
    "E_1012": "毒晶蛛刃",
    "E_3005": "幽影蛛袍",
    "E_4018": "絕情毒蕊",
    # 兔寶寶提莫：木杖/吹箭筒、花形吊飾、銀靴。
    "E_1013": "毒菇吹箭",
    "E_4017": "致幻菌傘",
    "E_5005": "狡兔戰靴",
    # 圖奇：紫弓、鼠形圖騰、青綠靴。
    "E_1005": "瘟疫之弩",
    "E_4001": "疫鼠圖騰",
    "E_5010": "潛行鼠靴",
    # ---- 2026-10-24 全裝備命名：剩餘的所有模板（依槽位與定位） ----
    # 武器：輸出（刃/弓/法杖）
    "E_1002": "青鋒短刃", "E_1004": "赤焰長弓", "E_1011": "霜紋細劍",
    "E_1014": "幽影匕首", "E_1015": "逐風長槍", "E_1019": "流星之弓",
    "E_1020": "裁決之刃", "E_1021": "夜梟之弩", "E_1024": "疾風雙刃",
    "E_1025": "破曉之弓", "E_1027": "虛空之刃", "E_1029": "月華法杖",
    "E_1033": "血月彎刀", "E_1041": "銀翼長弓",
    # 武器：戰士（斧/錘/戟）
    "E_1003": "裂風戰斧", "E_1006": "碎岩巨錘", "E_1016": "斷嶽戰斧",
    "E_1017": "裂地重錘", "E_1023": "狂瀾戰斧", "E_1051": "烈焰戰斧",
    "E_1061": "雷鳴重錘", "E_1499": "龍牙戰戟", "E_1999": "遠古戰戟",
    # 武器：坦克（盾/壁壘）
    "E_1018": "鐵壁巨盾", "E_1022": "守誓之盾", "E_1026": "磐石壁壘",
    "E_1028": "不滅之盾", "E_1031": "蒼穹壁壘", "E_1502": "聖光壁壘",
    "E_1503": "寒鐵壁壘", "E_1504": "星辰長劍", "E_1505": "烈陽戰刃",
    # 護甲
    "E_3001": "皮甲胸鎧", "E_3002": "鎖鏈軟甲", "E_3003": "秘銀戰鎧",
    "E_3004": "龍鱗重甲", "E_3006": "暗影鬥篷", "E_3008": "星辰法袍",
    "E_3999": "遠古聖鎧",
    # 飾品
    "E_4002": "紅玉戒指", "E_4007": "月影項鍊", "E_4009": "秘法之瞳",
    "E_4010": "獵鷹徽記", "E_4011": "守護符石", "E_4012": "烈焰吊墜",
    "E_4013": "冰晶耳飾", "E_4014": "大地徽章", "E_4015": "狂風護符",
    "E_4016": "聖光墜飾", "E_4019": "暗影指環", "E_4020": "星辰項鍊",
    "E_4021": "龍血護符", "E_4022": "虛空徽記", "E_4024": "雷霆戒指",
    "E_4027": "深海吊墜", "E_4999": "王者之戒",
    # 靴子
    "E_5001": "疾行戰靴", "E_5002": "皮革軟靴", "E_5003": "獵風長靴",
    "E_5004": "踏雲靴", "E_5006": "鎖甲戰靴", "E_5008": "迅影之靴",
    "E_5011": "龍鱗戰靴", "E_5016": "星辰步履", "E_5999": "遠古疾靴",
    # 技能書（2026-10-24 user redesign）
    "E_6002": "狂暴兇殺術", "E_6003": "狂暴裂甲",
    "E_6004": "狂暴鐵壁", "E_6005": "鷹眼精準術",
    "E_6006": "無影靈巧術", "E_6007": "狂暴致命",
    "E_6008": "狂暴攔截", "E_6010": "魔技：獻祭",
    "E_6501": "神技：狙殺", "E_6502": "神技：突襲",
    "E_6503": "神技：湧動", "E_6504": "神技：鐵腕",
    "E_6506": "神技：堅定",
}
# 2026-10-24 user-specified renames (original LoL-style item names).
EQUIP_NAME_OVERRIDES.update({
    "E_1002": "詭術法杖", "E_1003": "符文大劍", "E_1004": "古銅之刃",
    "E_1011": "沸騰之刃", "E_1014": "B179左輪手槍",
    "E_1015": "失落的瞄準鏡", "E_1017": "洽塔卡十字",
    "E_1018": "幽冥護手", "E_1019": "飛火流星", "E_1020": "聖石雙槍",
    "E_1021": "甜蜜之弩", "E_1022": "赤炎手套",
    "E_1024": "黃金突擊步槍", "E_1025": "冰冷之觸",
    "E_1026": "紫晶護手", "E_1027": "魚骨槍炮", "E_1028": "無羈的歌謠",
    "E_1029": "狩獵之牙", "E_1031": "不屈藥劑", "E_1033": "雷霆之刃",
    "E_1041": "破敗法杖", "E_1061": "秘銀匕首",
    "E_1503": "冰魄之心", "E_1504": "灼熱之盾", "E_1505": "寒鐵壁壘",
    "E_3006": "新年的鐘聲",
    "E_4002": "縛法寶珠", "E_4007": "月影皇冠", "E_4012": "古銅聖杯",
    "E_4013": "幽藍面紗", "E_4014": "動感耳機", "E_4020": "嶄新的玩偶",
    "E_4021": "小丑頭套", "E_4022": "龍牙項鍊", "E_4024": "暗影護符",
    "E_4027": "鋼之心", "E_4999": "混天綾", "E_5008": "小老虎布鞋",
})
for _eid, _meta in EQUIP_CATALOG.items():
    _base_eid = "_".join(str(_eid).split("_")[:2])
    if _base_eid in EQUIP_NAME_OVERRIDES:
        _meta["name"] = EQUIP_NAME_OVERRIDES[_base_eid]


def _endgame_affix_max(eid):
    """Max-level affix values for one equipment template."""
    _meta = EQUIP_CATALOG.get(eid) if isinstance(eid, str) else None
    _pl = (_meta or {}).get("pl") or []
    _out = {k: 0 for k in _EQUIP_AFFIX_MAX}
    if len(_pl) >= 8:
        for _name in (_pl[6], _pl[7]):
            if _name in _out:
                _out[_name] = _EQUIP_AFFIX_MAX[_name]
    return _out

HERE = os.path.dirname(os.path.abspath(__file__))
LOG_PATH = os.path.join(HERE, "server_log.txt")
# Legacy path only; accounts are stored in Turso since 2026-10-25.
STORE_PATH = os.path.join(HERE, "accounts.json")


def _load_dotenv(path):
    """Minimal .env reader so local runs keep secrets out of the repo."""
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, val = line.split("=", 1)
                key = key.strip()
                val = val.strip().strip('"').strip("'")
                if key and key not in os.environ:
                    os.environ[key] = val
    except FileNotFoundError:
        pass


_load_dotenv(os.path.join(HERE, ".env"))

TURSO_DATABASE_URL = os.environ.get("TURSO_DATABASE_URL", "").strip()
TURSO_AUTH_TOKEN = os.environ.get("TURSO_AUTH_TOKEN", "").strip()
# 2026-10-25: raw AMF hex contains the password on user.login/user.register.
# Keep it out of Render logs unless explicitly enabled for protocol debugging.
DEBUG_RAW_PACKETS = os.environ.get("GAME_DEBUG_RAW", "") == "1"
# 2026-10-25: Render (and most PaaS) inject the listening port as PORT.
# Keep GAME_SERVER_PORT for local runs; fall back to 8080.
PORT = int(os.environ.get("PORT", os.environ.get("GAME_SERVER_PORT", "8080")))

_log_lock = threading.Lock()
_EPOCH = datetime.datetime(1970, 1, 1)


def _now_ms():
    """UTC epoch milliseconds.

    datetime.utcnow().timestamp() interprets the naive value as *local*
    time, shifting every stored/compared timestamp by the UTC offset.
    """
    return int((datetime.datetime.utcnow() - _EPOCH).total_seconds() * 1000)


def log(*parts):
    line = " ".join(str(p) for p in parts)
    line = datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3] + "  " + line
    with _log_lock:
        print(line, flush=True)
        try:
            with open(LOG_PATH, "a", encoding="utf-8") as fh:
                fh.write(line + "\n")
        except Exception:
            pass


# 2026-10-24: zone picked on the login screen; the /notice page prints it.
_CURRENT_ZONE = "1-01"


# --------------------------------------------------------------------------- #
# Turso (libSQL) account storage
# --------------------------------------------------------------------------- #
_PLAYERS_DDL = (
    "CREATE TABLE IF NOT EXISTS players ("
    " account TEXT PRIMARY KEY,"
    " password_hash TEXT NOT NULL,"
    " nickname TEXT NOT NULL,"
    " created_at TEXT NOT NULL,"
    " data TEXT NOT NULL DEFAULT '{}'"
    ")"
)

_DB_CLIENT = None
_DB_LOCK = threading.RLock()


def _json_default(obj):
    if isinstance(obj, (datetime.datetime, datetime.date)):
        return obj.isoformat()
    return str(obj)


def _db_client():
    global _DB_CLIENT
    with _DB_LOCK:
        if _DB_CLIENT is None:
            if create_client_sync is None:
                raise RuntimeError(
                    "libsql-client is not installed "
                    "(pip install -r requirements.txt)")
            if not TURSO_DATABASE_URL:
                raise RuntimeError("TURSO_DATABASE_URL is not set")
            url = TURSO_DATABASE_URL
            # Turso hands out libsql:// URLs; the Python SDK speaks https.
            if url.startswith("libsql://"):
                url = "https://" + url[len("libsql://"):]
            _DB_CLIENT = create_client_sync(
                url=url, auth_token=TURSO_AUTH_TOKEN or None)
            # 2026-10-25: libsql-client builds its aiohttp session with the
            # 5-minute default timeout, so one dead connection used to block a
            # register/login for minutes.  Cap each HTTP attempt at 8s so the
            # retry loop and the client's own socket timeout stay in sync.
            try:
                import aiohttp
                _session = getattr(
                    getattr(_DB_CLIENT, "_client", None), "_session", None)
                if _session is not None:
                    _session._timeout = aiohttp.ClientTimeout(
                        total=8, connect=4, sock_read=6)
            except Exception:
                pass
            _DB_CLIENT.batch([_PLAYERS_DDL])
            log("turso connected:", url, "table=players")
        return _DB_CLIENT


def _db_with_retry(fn):
    """Run one DB call, reconnecting and retrying on transient Turso errors."""
    global _DB_CLIENT
    last = None
    for attempt in range(3):
        try:
            with _DB_LOCK:
                return fn(_db_client())
        except Exception as exc:        # network hiccups, expired sessions
            last = exc
            if isinstance(exc, KeyError):
                # libsql-client turns a Turso status envelope (HTTP 200 +
                # {"message","code"}, e.g. SQLITE_CONSTRAINT) into KeyError
                # because there is no "result" field.  That is a SQL answer,
                # not a network problem: retrying cannot help.
                raise
            _DB_CLIENT = None           # force a fresh client next attempt
            try:
                log("db retry %d/3: %s" % (attempt + 1, exc))
            except Exception:
                pass
            time.sleep(0.35 * (attempt + 1))
    raise last


def _db_execute(sql, params=None):
    return _db_with_retry(
        lambda client: client.execute(sql, list(params or [])))


def _db_batch(statements):
    return _db_with_retry(lambda client: client.batch(statements))


def init_db():
    """Create the schema at startup and fail fast on a bad configuration."""
    _db_execute("SELECT 1")


def _account_row(account):
    rs = _db_execute(
        "SELECT password_hash,nickname,created_at,data"
        " FROM players WHERE account=?", [account])
    return rs.rows[0] if rs.rows else None


def _random_token():
    return "%016x" % random.getrandbits(64)


def hash_password(password):
    if bcrypt is None:
        raise RuntimeError(
            "bcrypt is not installed (pip install -r requirements.txt)")
    return bcrypt.hashpw(str(password).encode("utf-8"),
                         bcrypt.gensalt()).decode("ascii")


def _password_matches(password_hash, password):
    if bcrypt is None or not password_hash:
        return False
    try:
        return bcrypt.checkpw(str(password).encode("utf-8"),
                              str(password_hash).encode("utf-8"))
    except (ValueError, TypeError):
        return False


def verify_account_password(account, password, row=None):
    """Check a password against the stored bcrypt hash.

    `row` may be passed when the caller already loaded the players row (the
    login handler gets it from the TursoAccountStore cache), which saves a
    whole network round trip per login.
    """
    if row is None:
        row = _account_row(account)
    if row is None:
        return False
    return _password_matches(row[0], password)


class AccountExistsError(ValueError):
    """Raised when INSERT hits the players.account primary key."""


def _insert_account(account, password, acc):
    """INSERT one full player row (single round trip)."""
    now = datetime.datetime.utcnow().isoformat()
    acc["created_at"] = now
    try:
        _db_execute(
            "INSERT INTO players(account,password_hash,nickname,created_at,data)"
            " VALUES(?,?,?,?,?)",
            [account, hash_password(password),
             str(acc.get("nick") or account), now,
             json.dumps(acc, ensure_ascii=False, default=_json_default)])
    except KeyError:
        # Turso answers a duplicate primary key with HTTP 200 and a
        # {"message":"SQLite error: UNIQUE constraint failed...","code":
        # "SQLITE_CONSTRAINT"} body, which libsql-client surfaces as
        # KeyError('result').  Confirm with a row lookup so other SQL
        # errors are not misreported as "account exists".
        if _account_row(account) is not None:
            raise AccountExistsError(account)
        raise
    except Exception as exc:
        msg = str(exc).lower()
        if "unique" in msg or "constraint" in msg:
            raise AccountExistsError(account)
        raise


def create_account(account, password, nickname=None):
    """INSERT a new player row.  Raises ValueError when it already exists."""
    acc = new_account(account, "")
    acc["nick"] = nickname or account
    acc["sessionid"] = _random_token()
    acc["auto_token"] = _random_token()
    _insert_account(account, password, acc)
    return acc


def _upsert_account(account, acc):
    _db_execute(
        "UPDATE players SET data=?, nickname=? WHERE account=?",
        [json.dumps(acc, ensure_ascii=False, default=_json_default),
         str(acc.get("nick") or account), account])


_ACCOUNT_RE = re.compile(r"^[A-Za-z0-9]{4,16}$")


def _validate_account_name(account):
    if not account:
        return "請輸入帳號"
    if not _ACCOUNT_RE.match(account):
        return "帳號僅支持字母和數字，長度 4-16 位"
    return ""


def _validate_password(password):
    if not password:
        return "請輸入密碼"
    if len(password) < 6:
        return "密碼長度至少 6 位"
    return ""


def _validate_account(account, password):
    return _validate_account_name(account) or _validate_password(password)


class TursoAccountStore:
    """Dict-like view over the players table.

    Handlers call accounts.get(uid) / save_accounts(accounts); each store
    caches only the rows touched by one AMF request and writes them back.
    """

    def __init__(self):
        self._cache = {}
        self._raw = {}
        self._dirty = set()

    def _load(self, uid):
        row = _account_row(uid)
        if row is None:
            return None
        self._raw[uid] = row
        try:
            acc = json.loads(row[3] or "{}")
        except (TypeError, ValueError):
            acc = {}
        if not isinstance(acc, dict):
            acc = {}
        acc.setdefault("uid", uid)
        acc.setdefault("session_key", uid)
        acc.setdefault("sessionid", "")
        self._cache[uid] = acc
        return acc

    def peek_row(self, uid):
        """Return the raw players row for uid, using the cache when loaded."""
        uid = str(uid)
        if uid not in self._raw:
            row = _account_row(uid)
            if row is not None:
                self._raw[uid] = row
        return self._raw.get(uid)

    def check_password(self, uid, password):
        row = self.peek_row(uid)
        if row is None:
            return False
        return _password_matches(row[0], password)

    def put_clean(self, uid, acc):
        """Remember a row that was just written, without marking it dirty."""
        uid = str(uid)
        self._cache[uid] = acc
        self._dirty.discard(uid)

    def get(self, uid, default=None):
        if uid is None:
            return default
        uid = str(uid)
        if uid not in self._cache and self._load(uid) is None:
            return default
        return self._cache.get(uid, default)

    def __contains__(self, uid):
        return self.get(uid) is not None

    def __getitem__(self, uid):
        acc = self.get(uid)
        if acc is None:
            raise KeyError(uid)
        return acc

    def __setitem__(self, uid, acc):
        uid = str(uid)
        self._cache[uid] = acc
        self._dirty.add(uid)

    def __delitem__(self, uid):
        uid = str(uid)
        self._cache.pop(uid, None)
        self._dirty.discard(uid)

    def save(self):
        for uid in list(self._dirty):
            acc = self._cache.get(uid)
            if acc is not None:
                _upsert_account(uid, acc)
        self._dirty.clear()


def load_accounts():
    return TursoAccountStore()


def save_accounts(data):
    if isinstance(data, TursoAccountStore):
        data.save()
    elif isinstance(data, dict):
        for uid, acc in data.items():
            if isinstance(acc, dict):
                _upsert_account(str(uid), acc)


# --------------------------------------------------------------------------- #
# AMF packet plumbing
# --------------------------------------------------------------------------- #
def _parse_at(body, off):
    """Parse an AMF0 packet whose first field ends at `off`."""
    r = Reader(body)
    r.p = off
    headers = []
    hc = r.u16()
    if hc > 4096:
        raise ValueError("implausible header count %d" % hc)
    for _ in range(hc):
        name = r.str16()
        r.u8()                   # must understand
        n = r.u32()
        val = read_amf0(Reader(r.take(n))) if n else None
        headers.append((name, val))
    mc = r.u16()
    if mc > 4096:
        raise ValueError("implausible message count %d" % mc)
    messages = []
    for _ in range(mc):
        target = r.str16()
        response = r.str16()
        n = r.u32()
        raw = r.take(n)
        decoded = read_amf0(Reader(raw))
        messages.append((target, response, decoded))
    if r.p != len(body):
        raise ValueError("trailing bytes: consumed %d of %d" % (r.p, len(body)))
    return headers, messages


def parse_packet(body):
    """Return (headers, messages); each message is (target, response, decoded).

    The AIR runtime's packet starts with a 2-byte version field; other clients
    use 1 byte.  Try both and keep whichever consumes the body exactly.
    """
    last = None
    for off in (2, 1):
        try:
            return _parse_at(body, off)
        except Exception as exc:
            last = exc
    raise last


VARIANTS = [
    "v2-amf0array-amf3",     # 00 03 | 0A n 11 <amf3>
    "v2-amf0array-amf0",     # 00 03 | 0A n    <amf0>
    "v2-amf3direct",         # 00 03 | 11 <amf3>
    "v2-amf0direct",         # 00 03 | <amf0>
]
_variant_counter = [0]

# Reply format the AIR client actually accepts (verified against a real
# NetConnection, see testcall/TestCall.as):
#   target = "<request response uri>/onResult"  (AMF0 spec 4.1.3)
#   response = ""
#   body   = 0x11 + AMF3 result object, NOT wrapped in an array
#            (Flash passes the decoded body straight to the Responder, so a
#             wrapper array would break param1["params"] with error #1010)
VARIANT_OK = "direct-amf3"


BODY_KINDS = ["a1-amf3", "a1-amf0", "a1-amf3str", "direct-amf0",
              "a2null-amf0", "a2obj-amf0"]


def _encode_result(result, variant):
    if variant == "amf0string":
        return b"\x02\x00\x02hi"
    if variant.endswith("amf0array-amf3"):
        return b"\x0a" + struct.pack(">I", 1) + b"\x11" + encode_amf3(result)
    if variant.endswith("amf0array-amf0"):
        return b"\x0a" + struct.pack(">I", 1) + encode_amf0(result)
    if variant.endswith("amf3direct"):
        return b"\x11" + encode_amf3(result)
    if variant == "a1-amf3":
        return b"\x0a" + struct.pack(">I", 1) + b"\x11" + encode_amf3(result)
    if variant == "direct-amf3":
        return b"\x11" + encode_amf3(result)
    if variant == "a1-amf0":
        return b"\x0a" + struct.pack(">I", 1) + encode_amf0(result)
    if variant == "a1-amf3str":
        return b"\x0a" + struct.pack(">I", 1) + b"\x11" + encode_amf3("ok")
    if variant == "a2null-amf0":
        return (b"\x0a" + struct.pack(">I", 2) + b"\x05" + encode_amf0(result))
    if variant == "a2obj-amf0":
        return (b"\x0a" + struct.pack(">I", 2) + encode_amf0(result) + b"\x05")
    return encode_amf0(result)          # direct-amf0


# AMF0 spec 4.1.3: a response's target URI is the request's response URI with
# "/onResult" appended for success ("/onStatus" for a failure).
TARGET_KINDS = ["$URI/onResult", "$URI/onStatus", "$URI", "", "http_api", "null"]
RESP_KINDS = ["", "null", "$URI"]
BIG_COMBOS = [(t, r, b)
              for t in TARGET_KINDS
              for r in RESP_KINDS
              for b in BODY_KINDS]


# target / response URI combinations to try; "$URI" = the caller's response uri
URI_COMBOS = [
    ("$URI/onResult", ""),   # 0: what the AMF0 spec prescribes (VERIFIED working)
    ("$URI", "null"),    # 1
    ("$URI", "$URI"),    # 2
    ("", "$URI"),        # 3
    ("", "null"),        # 4
    ("", ""),            # 5
    ("http_api", "$URI"),  # 6
    ("http_api", ""),    # 7
    ("null", "$URI"),    # 8
    ("null", ""),        # 9
    ("$URI", "http_api"),  # 10
    ("http_api", "http_api"),  # 11
]


def _uri_field(raw):
    """target/response URIs are plain UTF-8 with a u16 length prefix - they must
    NOT go through the AMF0 string encoder (that adds a 0x02 marker and makes
    Flash read a bogus length, which showed up as Client.Data.UnderFlow)."""
    b = raw.encode("utf-8")
    return struct.pack(">H", len(b)) + b


def build_packet(replies, version_bytes=b"\x00\x03", variant=None):
    """replies: list of (target, response, result_object)."""
    if variant is None:
        variant = VARIANT_OK      # the one verified against the real client
    _variant_counter[0] += 1

    ver_mode = os.environ.get("GAME_VER_MODE", "echo")
    if ver_mode == "echo":
        ver = version_bytes if len(version_bytes) == 2 else b"\x00\x03"
    elif ver_mode == "zero2":
        ver = b"\x00\x00"
    elif ver_mode == "zero1":
        ver = b"\x00"
    else:                                   # zero4
        ver = b"\x00\x00\x00\x00"
    out = bytearray()
    out += ver
    out += struct.pack(">H", 0)             # header count
    out += struct.pack(">H", len(replies))  # one reply message per request
    for tgt, resp, own_variant, result in replies:
        payload = _encode_result(result, own_variant or variant)
        out += _uri_field(tgt)
        out += _uri_field(resp)
        out += struct.pack(">I", len(payload))
        out += payload
    return bytes(out), variant


def find_call(node):
    """Recursively locate the (method, params) pair inside a decoded request."""
    if isinstance(node, dict):
        m = node.get("method")
        if isinstance(m, str) and "." in m and isinstance(node.get("params"), dict):
            return node
        for v in node.values():
            got = find_call(v)
            if got:
                return got
    elif isinstance(node, list):
        for v in node:
            got = find_call(v)
            if got:
                return got
    return None


# --------------------------------------------------------------------------- #
# service implementations
# --------------------------------------------------------------------------- #
def _stage(name, line_count, enemies, energy, exp, gold):
    """Build one combat_main entry.

    enemies: tuples of (avatarId, level, lane, pos)

    `pos` below is authored as a "depth from the enemy back line" (0.85 is the
    enemy front row, 0.62 the second row).  GameMap.initAvatar feeds team2's
    value straight to Avatar.goFight(2, line, pos/LINE_POS), and that maps to
    y = pos * LANDFORM_POS + PIXEL_BASE_Y: larger values sit at the *bottom*
    of the lane, i.e. right in front of our own team (which embarks at
    0.65..1.0).  Mirroring the value flips the enemy formation to the top of
    the map so both sides start apart and face each other.
    Map-lineup form: [aid, lv, slv, line, pos, leader, dropRate, dropLv, dropId]
    """
    # All lanes use the SAME background.  Mixing mg001/mg002/mg003 made the
    # client build the three lanes at different heights/anchors, so a
    # whole-team buff could appear on some lanes earlier than on others.
    _bg = ("m001", "m002", "m003")[sum(ord(_c) for _c in name) % 3]
    return {
        "name": name,
        "line": [line_count, [_bg, _bg, _bg]],
        "team1": [],
        "team2": [[aid, lv, 1, lane, round(1.0 - pos, 2), 0, 0.6, 5, aid]
                  for (aid, lv, lane, pos) in enemies],
        # victory condition: -1 = 全面取勝 (wipe the enemy team)
        "win": [-1],
        "energy": energy,
        "exp": exp,
        "gold": gold,
        # ItemPVEcombat requires limit[diff] > 0 to let the player start.
        # diff 0 = normal, diff 1 = hard; both must be present or getLimit(1)
        # returns undefined and clicking a hard stage shows 獎勵已領取 (90031).
        "limit": [9999, 9999],
        "pre": [],
        "new_4attrs": [0, 0, 0, 0],
        "equip_drop": [],
    }


# The damage-test stage lives in the normal PVE tab as chapter 1's 5th stage.
# (It used to be an activity dungeon, but the W_* map path made the client's
# map loader stall on the custom enemies.)
TEST_STAGE_ID = "M_011_5"
PREVIEW_STAGE_ID = "M_011_6"
HARD_TEST_STAGE_ID = "M_011_7"
INFERNO_TEST_STAGE_ID = "M_011_8"
HELL2_TEST_STAGE_ID = "M_011_9"
HELL3_TEST_STAGE_ID = "M_011_10"
DEBUFF_TEST_STAGE_ID = "M_011_11"
TEST_STAGE_IDS = {TEST_STAGE_ID, PREVIEW_STAGE_ID, HARD_TEST_STAGE_ID,
                  INFERNO_TEST_STAGE_ID, HELL2_TEST_STAGE_ID,
                  HELL3_TEST_STAGE_ID, DEBUFF_TEST_STAGE_ID}

# 2026-10-25: every 战斗试炼 (W_TRIAL_1..7) stage pays exp on each clear.
# Range is 100..2000 as requested; values ramp with the dummy difficulty.
TRIAL_STAGE_EXP = [100, 100, 300, 500, 800, 1200, 1500]

# ---------------------------------------------------------------------------
# 2026-10-24 普通/困難副本 40 章
# ---------------------------------------------------------------------------
PVE_CHAPTER_COUNT = 40
PVE_FIRST_CHAPTER = 11          # M_011 .. M_050
PVE_STAGES_PER_CHAPTER = 4      # 3 平常關 + 1 把關關
# gallery 193-211：野怪（A_3001..A_4015，共 19 族）。
PVE_WILD_MONSTERS = [
    "A_3001", "A_3002", "A_3003", "A_3004", "A_3005", "A_3006",
    "A_3007", "A_3008", "A_3009", "A_3010", "A_4001", "A_4004",
    "A_4005", "A_4006", "A_4007", "A_4008", "A_4012", "A_4014",
    "A_4015",
]
# gallery 214-224：建築材料（全部建築）。
PVE_BUILDINGS = [
    "A_5001", "A_5002", "A_5003", "A_5004", "A_5005", "A_5006",
    "A_5007", "A_5008", "A_5009", "A_5010", "A_5011",
]
# 進階英雄（gallery 22-32/37/39-42/49/51-53/57/59/60/62/67/68/75/108）。
PVE_ADVANCED_HEROES = [
    "A_1022", "A_1023", "A_1024", "A_1025", "A_1026", "A_1027",
    "A_1028", "A_1029", "A_1030", "A_1032", "A_1033", "A_1049",
    "A_1053", "A_1054", "A_1056", "A_1060", "A_1078", "A_1081",
    "A_1082", "A_1083", "A_1093", "A_1095", "A_1096", "A_1098",
    "A_1106", "A_1108", "A_1119", "A_1212",
]

PVE_CHAPTER_NAMES = [
    "試煉之地", "迷霧沼澤", "冰封峽谷", "熔岩裂谷", "天空迴廊",
    "王座前廳", "暗月荒原", "深淵迴廊", "星隕平原", "終焉之門",
    "赤焰魔域", "蒼穹之海", "幽影王陵", "時空裂隙", "龍脊山脈",
    "深淵海溝", "雷電荒原", "水晶洞窟", "虛空邊境", "榮耀之巔",
    "黃昏沙海", "血月森林", "古代遺跡", "寒霜要塞", "烈焰礦坑",
    "毒霧沼地", "風暴群島", "暗影城塞", "龍語高地", "星辰祭壇",
    "血色峽谷", "亡者墓園", "鐵壁要塞", "晶石礦脈", "虛無深淵",
    "雷霆神殿", "極光冰原", "混沌荒原", "天穹之門", "最強王座",
]
PVE_STAGE_SUFFIX = ("前哨", "腹地", "核心", "王座")
PVE_BOSS_PREFIX = "A_8"       # synthetic gatekeeper boss cards (A_8022_6 …)


def _pve_best_star(fam):
    """Highest real star tier that exists in the avatar catalog for a family."""
    stars = []
    for _aid in AVATAR_CATALOG:
        if _aid.rsplit("_", 1)[0] == fam:
            try:
                stars.append(int(_aid.rsplit("_", 1)[1]))
            except (IndexError, ValueError):
                pass
    return "%s_%d" % (fam, max(stars) if stars else 1)


def _pve_boss_family(fam):
    """A_1022 -> A_8022 (enemy-only gatekeeper copy)."""
    try:
        return PVE_BOSS_PREFIX + str(int(fam.split("_")[1]))
    except (IndexError, ValueError):
        return fam


_PVE_BOSS_FAMILY_MAP = {
    _pve_boss_family(_fam): _fam for _fam in PVE_ADVANCED_HEROES
}


def _pve_unit_allowed(aid):
    """Dungeon appearance rule (2026-10-24).

    Heroes (A_1), monsters (A_2/A_3/A_4) and buildings (A_5) may appear as
    dungeon units.  #164 (A_2107, 技能餅乾-小) and the material families
    (A_6xxx, gallery 225-256) may not.
    """
    fam = str(aid).rsplit("_", 1)[0]
    if fam in _PVE_BOSS_FAMILY_MAP:
        return True
    if fam == "A_2107":
        return False
    return fam.startswith(("A_1", "A_2", "A_3", "A_4", "A_5"))


def _pve_sanitize_units(aids):
    """Replace forbidden dungeon units with a plain wild monster."""
    out = []
    for aid in aids:
        out.append(aid if _pve_unit_allowed(aid) else "A_3001_2")
    return out


def _pve_chapter_index(cid):
    """'M_011_4' -> 0; unknown ids clamp to 0."""
    try:
        return max(0, int(str(cid).split("_")[1]) - PVE_FIRST_CHAPTER)
    except (IndexError, ValueError):
        return 0


def _pve_gatekeepers(chapter_index):
    """1-3 advanced heroes guarding the chapter's final stage.

    A_1212 has no 5★ card (only 6★), so it is always paired with a second
    gatekeeper to keep the hard-mode 5★ drop rule satisfiable.
    """
    if chapter_index < 10:
        n = 1
    elif chapter_index < 26:
        n = 2
    else:
        n = 3
    out = []
    for k in range(n):
        fam = PVE_ADVANCED_HEROES[
            (chapter_index * 3 + k) % len(PVE_ADVANCED_HEROES)]
        if fam not in out:
            out.append(fam)
    if "A_1212" in out and len(out) < 2:
        for fam in PVE_ADVANCED_HEROES:
            if fam != "A_1212" and fam not in out:
                out.append(fam)
                break
    return out


def _pve_positions(aids, level, lanes):
    """Assign lanes/rows so no two units in a lane share the same depth."""
    out = []
    per_lane = {}
    for aid in aids:
        lane = 0
        # distribute round-robin, but keep rows inside a lane sequential
        lane = len(out) % lanes
        row = per_lane.get(lane, 0)
        per_lane[lane] = row + 1
        pos = (0.85, 0.72, 0.62, 0.55)[min(row, 3)]
        out.append((aid, level, lane, pos))
    return out


def _pve_stage(name, aids, level, energy, exp, gold):
    """One 40-chapter stage; drops are handled server-side (no client rolls)."""
    aids = _pve_sanitize_units(list(aids))
    n = len(aids)
    lanes = 1 if n <= 2 else (2 if n <= 4 else 3)
    stage = _stage(name, lanes, _pve_positions(aids, level, lanes),
                   energy, exp, gold)
    for enemy in stage["team2"]:
        enemy[6] = 0      # dropRate
        enemy[8] = ""     # dropId
    return stage


def _pve_stage_exp(chapter_index, stage_no):
    """2026-10-25 exp redistribution (summoner max level 60).

    Reaching 60 from 25 costs 100*(25+..+59) = 147,000 exp.  Story stages use
    this ramp and the server grants the base value (normal) or 2x (hard) --
    first clears do NOT double exp any more, so the settlement panel shows
    exactly what is granted.  All 320 normal+hard first clears total ~108,800
    exp, i.e. ~74% of the 147,000 needed, leaving the rest to repeat clears,
    test stages, crops and other systems.
    """
    base = 100 + int(round(400.0 * chapter_index / 39.0))
    return base + (0, 20, 40, 100)[stage_no - 1]


def _pve_generated_stage(chapter_index, stage_no):
    """Compose one normal-dungeon stage.

    Regular stages: 193-211 野怪 + all buildings.
    Final stage: ≤3 advanced-hero gatekeepers + one wild monster and one
    building.  Materials and #164 (A_2107) never appear.
    """
    chapter = PVE_FIRST_CHAPTER + chapter_index
    ci = chapter_index
    level = 3 + ci * 2 + (stage_no - 1) * 2
    if stage_no < PVE_STAGES_PER_CHAPTER:
        mon_start = ci * 3 + stage_no * 2
        if stage_no == 1:
            aids = [ _pve_best_star(PVE_WILD_MONSTERS[
                        (mon_start + j) % len(PVE_WILD_MONSTERS)])
                     for j in range(3) ]
        elif stage_no == 2:
            aids = [ _pve_best_star(PVE_WILD_MONSTERS[
                        (mon_start + j) % len(PVE_WILD_MONSTERS)])
                     for j in range(2) ]
            aids.append(_pve_best_star(PVE_BUILDINGS[
                (ci * 2 + stage_no) % len(PVE_BUILDINGS)]))
        else:
            aids = [ _pve_best_star(PVE_WILD_MONSTERS[
                        (mon_start + j) % len(PVE_WILD_MONSTERS)])
                     for j in range(2) ]
            aids.append(_pve_best_star(PVE_BUILDINGS[
                (ci * 2 + stage_no) % len(PVE_BUILDINGS)]))
            aids.append(_pve_best_star(PVE_BUILDINGS[
                (ci * 2 + stage_no + 4) % len(PVE_BUILDINGS)]))
        level += 0
    else:
        # 把關關：最多 3 名進階英雄 + 野怪 + 建築材料。
        gatekeepers = _pve_gatekeepers(ci)
        aids = [_pve_boss_family(fam) + "_6" for fam in gatekeepers]
        aids.append(_pve_best_star(PVE_WILD_MONSTERS[
            (ci * 5 + 3) % len(PVE_WILD_MONSTERS)]))
        aids.append(_pve_best_star(PVE_BUILDINGS[
            (ci * 3 + 7) % len(PVE_BUILDINGS)]))
        level += 6
    name = "%s·%s" % (PVE_CHAPTER_NAMES[ci],
                      PVE_STAGE_SUFFIX[stage_no - 1])
    return _pve_stage(name, aids, level,
                      6 + min(24, ci), _pve_stage_exp(ci, stage_no),
                      100 + ci * 400)


def _preview_stage_map():
    """One-lane dummy used to show every effect id for buff mapping."""
    stage = _stage("對單測試", 1, [
        ("A_2995_4", 50, 0, 0.85),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    for enemy in stage["team2"]:
        enemy[6] = 0
        enemy[8] = ""
    return stage


def _test_stage_map():
    """Three lanes, 3x #138 plus #139/#140/#141, zero stamina/rewards."""
    stage = _stage("傷害測試·三路", 3, [
        ("A_2996_4", 50, 0, 0.85),
        ("A_2996_4", 50, 1, 0.85),
        ("A_2996_4", 50, 2, 0.85),
        # 2026-10-20 user request: three more dummies, one per lane, so the
        # full-lane 能量衝擊 has 3 targets in every lane.
        ("A_2996_4", 50, 0, 0.72),
        ("A_2997_6", 70, 1, 0.72),
        ("A_2998_6", 70, 2, 0.72),
        ("A_2997_6", 70, 0, 0.62),
        ("A_2998_6", 70, 1, 0.62),
        ("A_2999_6", 70, 2, 0.62),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    for enemy in stage["team2"]:
        enemy[6] = 0      # dropRate
        enemy[8] = ""     # dropId
    return stage


def _test_hard_stage_map():
    """Hard damage test: same 9-dummy formation, 2x HP and real defences."""
    stage = _stage("傷害測試·三路·困難", 3, [
        ("A_2986_4", 50, 0, 0.85),
        ("A_2986_4", 50, 1, 0.85),
        ("A_2986_4", 50, 2, 0.85),
        ("A_2986_4", 50, 0, 0.72),
        ("A_2987_6", 70, 1, 0.72),
        ("A_2988_6", 70, 2, 0.72),
        ("A_2987_6", 70, 0, 0.62),
        ("A_2988_6", 70, 1, 0.62),
        ("A_2989_6", 70, 2, 0.62),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    for enemy in stage["team2"]:
        enemy[6] = 0      # dropRate
        enemy[8] = ""     # dropId
    return stage


def _test_inferno_stage_map():
    """Inferno damage test: 1.2M HP, 20k both defences, 40% crit resist."""
    stage = _stage("傷害測試·三路·煉獄", 3, [
        ("A_2976_4", 50, 0, 0.85),
        ("A_2976_4", 50, 1, 0.85),
        ("A_2976_4", 50, 2, 0.85),
        ("A_2976_4", 50, 0, 0.72),
        ("A_2977_6", 70, 1, 0.72),
        ("A_2978_6", 70, 2, 0.72),
        ("A_2977_6", 70, 0, 0.62),
        ("A_2978_6", 70, 1, 0.62),
        ("A_2979_6", 70, 2, 0.62),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    # GameMapData.initAvatarNew4attrs applies these to the enemy team:
    # [hit, flee, crit, tough]; tough is in 0.1% units, so 400 = 40% crit
    # resistance.
    stage["new_4attrs"] = [0, 0, 0, 400]
    for enemy in stage["team2"]:
        enemy[6] = 0      # dropRate
        enemy[8] = ""     # dropId
    return stage


def _test_hell2_stage_map():
    """Hell II: 2x the inferno limits (2.4M HP, 40k defences, 80% tough)."""
    stage = _stage("傷害測試·三路·地獄II", 3, [
        ("A_2966_4", 50, 0, 0.85),
        ("A_2966_4", 50, 1, 0.85),
        ("A_2966_4", 50, 2, 0.85),
        ("A_2966_4", 50, 0, 0.72),
        ("A_2967_6", 70, 1, 0.72),
        ("A_2968_6", 70, 2, 0.72),
        ("A_2967_6", 70, 0, 0.62),
        ("A_2968_6", 70, 1, 0.62),
        ("A_2969_6", 70, 2, 0.62),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    stage["new_4attrs"] = [0, 0, 0, 800]
    for enemy in stage["team2"]:
        enemy[6] = 0
        enemy[8] = ""
    return stage


def _test_hell3_stage_map():
    """Hell III: 4x the inferno limits (4.8M HP, 80k defences, 160% tough)."""
    stage = _stage("傷害測試·三路·地獄III", 3, [
        ("A_2956_4", 50, 0, 0.85),
        ("A_2956_4", 50, 1, 0.85),
        ("A_2956_4", 50, 2, 0.85),
        ("A_2956_4", 50, 0, 0.72),
        ("A_2957_6", 70, 1, 0.72),
        ("A_2958_6", 70, 2, 0.72),
        ("A_2957_6", 70, 0, 0.62),
        ("A_2958_6", 70, 1, 0.62),
        ("A_2959_6", 70, 2, 0.62),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    stage["new_4attrs"] = [0, 0, 0, 1600]
    for enemy in stage["team2"]:
        enemy[6] = 0
        enemy[8] = ""
    return stage


def _test_debuff_stage_map():
    """負面測試: Hell III stats, each enemy casts ONE debuff on our whole team.

    Seven enemies (3/2/2) so every debuff type in Buff.LIST_DEBUFF —
    stun / silence / weak / sunder / poison / burn / evil — appears exactly
    once.  Zero stamina and no drops, like the other damage-test stages.
    """
    stage = _stage("傷害測試·三路·地獄III·負面", 3, [
        ("A_2936_4", 50, 0, 0.85),
        ("A_2937_4", 50, 0, 0.72),
        ("A_2938_4", 50, 0, 0.62),
        ("A_2939_4", 50, 1, 0.85),
        ("A_2940_4", 50, 1, 0.72),
        ("A_2941_4", 50, 2, 0.85),
        ("A_2942_4", 50, 2, 0.72),
    ], 0, 0, 0)
    stage["limit"] = [9999, 9999]
    stage["new_4attrs"] = [0, 0, 0, 1600]
    for enemy in stage["team2"]:
        enemy[6] = 0
        enemy[8] = ""
    return stage


def _combat_main():
    """Story stages: 20 chapters x 4 stages.

    Chapters 1-10 keep their hand-written lineups; the 4th "精英" stage of
    each chapter and chapters 11-20 are generated by _add_more_stages().
    """
    stages = {
        # ---- chapter 1: 1 lane, easy ----
        "M_011_1": _stage("试炼之地", 1,
                          [("A_2001_4", 1, 0, 0.85)], 6, 10, 100),
        "M_011_2": _stage("试炼之地", 1,
                          [("A_1001_2", 2, 0, 0.85)], 6, 12, 120),
        "M_011_3": _stage("试炼之地", 1,
                          [("A_1001_2", 2, 0, 0.72),
                           ("A_1012_4", 2, 0, 0.92)], 6, 15, 150),
        # ---- chapter 2: 2 lanes ----
        "M_012_1": _stage("迷雾沼泽", 2,
                          [("A_1028_5", 3, 0, 0.82),
                           ("A_1013_3", 3, 1, 0.82)], 7, 15, 150),
        "M_012_2": _stage("幽影森林", 2,
                          [("A_1028_5", 4, 0, 0.82),
                           ("A_1013_3", 4, 1, 0.82),
                           ("A_1001_2", 3, 0, 0.60)], 7, 18, 180),
        "M_012_3": _stage("暗影神殿", 2,
                          [("A_1028_5", 4, 0, 0.85),
                           ("A_1013_3", 4, 1, 0.85),
                           ("A_1001_2", 4, 0, 0.62),
                           ("A_1012_4", 4, 1, 0.62)], 8, 20, 200),
        # ---- chapter 3: 3 lanes ----
        "M_013_1": _stage("冰封峡谷", 3,
                          [("A_1019_4", 5, 0, 0.85),
                           ("A_1022_5", 5, 1, 0.85),
                           ("A_1029_5", 5, 2, 0.85)], 8, 20, 200),
        "M_013_2": _stage("霜狼巢穴", 3,
                          [("A_1019_4", 6, 0, 0.85),
                           ("A_1022_5", 6, 1, 0.85),
                           ("A_1029_5", 6, 2, 0.85),
                           ("A_1013_3", 5, 0, 0.62)], 9, 25, 250),
        "M_013_3": _stage("巨龙之巢", 3,
                          [("A_1019_4", 8, 0, 0.85),
                           ("A_1022_5", 8, 1, 0.85),
                           ("A_1029_5", 8, 2, 0.85),
                           ("A_1014_3", 7, 1, 0.62),
                           ("A_1028_5", 7, 2, 0.62)], 10, 30, 300),
        # ---- chapter 4: 3 lanes, fire theme ----
        "M_014_1": _stage("熔岩裂谷", 3,
                          [("A_1028_5", 9, 0, 0.85),
                           ("A_1019_4", 9, 1, 0.85),
                           ("A_1022_5", 9, 2, 0.85)], 10, 30, 300),
        "M_014_2": _stage("烈焰祭坛", 3,
                          [("A_1028_5", 9, 0, 0.85),
                           ("A_1019_4", 9, 1, 0.85),
                           ("A_1022_5", 9, 2, 0.85),
                           ("A_1012_4", 9, 0, 0.60)], 11, 35, 350),
        "M_014_3": _stage("炎魔王座", 3,
                          [("A_1028_5", 10, 0, 0.85),
                           ("A_1019_4", 10, 1, 0.85),
                           ("A_1022_5", 10, 2, 0.85),
                           ("A_1014_3", 9, 1, 0.62),
                           ("A_1029_5", 9, 2, 0.62)], 12, 40, 400),
        # ---- chapter 5: 3 lanes, sky theme ----
        "M_015_1": _stage("天空回廊", 3,
                          [("A_1019_4", 10, 0, 0.85),
                           ("A_1029_5", 10, 1, 0.85),
                           ("A_1014_3", 10, 2, 0.85)], 11, 40, 400),
        "M_015_2": _stage("浮空神殿", 3,
                          [("A_1019_4", 10, 0, 0.85),
                           ("A_1029_5", 10, 1, 0.85),
                           ("A_1014_3", 10, 2, 0.85),
                           ("A_1022_5", 10, 1, 0.60)], 12, 45, 450),
        "M_015_3": _stage("雷云之巅", 3,
                          [("A_1019_4", 11, 0, 0.85),
                           ("A_1029_5", 11, 1, 0.85),
                           ("A_1014_3", 11, 2, 0.85),
                           ("A_1028_5", 11, 0, 0.62),
                           ("A_1022_5", 11, 2, 0.62)], 13, 50, 500),
        # ---- chapter 6: 3 lanes, final throne ----
        "M_016_1": _stage("王座前厅", 3,
                          [("A_1029_5", 11, 0, 0.85),
                           ("A_1019_4", 11, 1, 0.85),
                           ("A_1028_5", 11, 2, 0.85)], 12, 50, 500),
        "M_016_2": _stage("王者回廊", 3,
                          [("A_1029_5", 11, 0, 0.85),
                           ("A_1019_4", 11, 1, 0.85),
                           ("A_1028_5", 11, 2, 0.85),
                           ("A_1022_5", 11, 0, 0.60),
                           ("A_1014_3", 11, 2, 0.60)], 13, 55, 550),
        "M_016_3": _stage("最强王座", 3,
                          [("A_1019_4", 12, 0, 0.85),
                           ("A_1029_5", 12, 1, 0.85),
                           ("A_1028_5", 12, 2, 0.85),
                           ("A_1022_5", 12, 1, 0.62),
                           ("A_1014_3", 12, 2, 0.62),
                           ("A_2001_4", 12, 0, 0.55)], 15, 60, 600),
        # ---- chapters 7-10: expanded roster, longer stamina curve --------
        "M_017_1": _stage("暗月荒原", 3,
                          [("A_1101_6", 13, 0, 0.85),
                           ("A_1201_6", 13, 1, 0.85),
                           ("A_1309_6", 13, 2, 0.85)], 14, 70, 700),
        "M_017_2": _stage("血月峡谷", 3,
                          [("A_1101_6", 13, 0, 0.85),
                           ("A_1201_6", 13, 1, 0.85),
                           ("A_1309_6", 13, 2, 0.85),
                           ("A_1204_6", 12, 1, 0.62)], 15, 78, 780),
        "M_017_3": _stage("荒原王陵", 3,
                          [("A_1101_6", 14, 0, 0.85),
                           ("A_1201_6", 14, 1, 0.85),
                           ("A_1309_6", 14, 2, 0.85),
                           ("A_1206_6", 13, 0, 0.62),
                           ("A_1209_6", 13, 2, 0.62)], 16, 85, 850),
        "M_018_1": _stage("深渊回廊", 3,
                          [("A_1997_6", 15, 0, 0.85),
                           ("A_6992_6", 15, 1, 0.85),
                           ("A_6993_5", 15, 2, 0.85)], 16, 90, 900),
        "M_018_2": _stage("噬魂深渊", 3,
                          [("A_1997_6", 16, 0, 0.85),
                           ("A_6992_6", 16, 1, 0.85),
                           ("A_6993_5", 16, 2, 0.85),
                           ("A_6994_6", 15, 0, 0.62)], 17, 100, 1000),
        "M_018_3": _stage("深渊主宰", 3,
                          [("A_1997_6", 17, 0, 0.85),
                           ("A_6992_6", 17, 1, 0.85),
                           ("A_6994_6", 17, 2, 0.85),
                           ("A_6996_5", 16, 1, 0.62),
                           ("A_6997_5", 16, 2, 0.62)], 18, 110, 1100),
        "M_019_1": _stage("星陨平原", 3,
                          [("A_6998_5", 18, 0, 0.85),
                           ("A_6999_5", 18, 1, 0.85),
                           ("A_1204_6", 18, 2, 0.85)], 18, 120, 1200),
        "M_019_2": _stage("星界裂隙", 3,
                          [("A_6998_5", 19, 0, 0.85),
                           ("A_6999_5", 19, 1, 0.85),
                           ("A_1204_6", 19, 2, 0.85),
                           ("A_1206_6", 18, 0, 0.62)], 19, 130, 1300),
        "M_019_3": _stage("星界神殿", 3,
                          [("A_6998_5", 20, 0, 0.85),
                           ("A_6999_5", 20, 1, 0.85),
                           ("A_1209_6", 20, 2, 0.85),
                           ("A_1101_6", 20, 1, 0.62),
                           ("A_1997_6", 20, 2, 0.62)], 20, 140, 1400),
        "M_020_1": _stage("终焉之门", 3,
                          [("A_6996_5", 22, 0, 0.85),
                           ("A_6997_5", 22, 1, 0.85),
                           ("A_6998_5", 22, 2, 0.85)], 20, 150, 1500),
        "M_020_2": _stage("终焉回廊", 3,
                          [("A_6996_5", 23, 0, 0.85),
                           ("A_6997_5", 23, 1, 0.85),
                           ("A_6998_5", 23, 2, 0.85),
                           ("A_6999_5", 23, 0, 0.62)], 22, 175, 1750),
        "M_020_3": _stage("终焉王座", 3,
                          [("A_6996_5", 25, 0, 0.85),
                           ("A_6997_5", 25, 1, 0.85),
                           ("A_6998_5", 25, 2, 0.85),
                           ("A_6999_5", 25, 1, 0.62),
                           ("A_1997_6", 25, 2, 0.62),
                           ("A_6992_6", 25, 0, 0.55)], 25, 200, 2000),
    }
    _add_more_stages(stages)
    # 2026-10-24: the old damage-test maps moved to the 活動 tab (W_TRIAL).
    return stages


def _combat_main_40():
    """2026-10-24: 40 chapters x 4 generated stages.

    The old damage-test / preview / hell maps now live in the 活動 tab as the
    战斗试炼 category (cfg.battle_ploy/combat_ploy W_TRIAL_1..7).
    """
    stages = {}
    for ci in range(PVE_CHAPTER_COUNT):
        chapter = PVE_FIRST_CHAPTER + ci
        for s in range(1, PVE_STAGES_PER_CHAPTER + 1):
            stages["M_%03d_%d" % (chapter, s)] = _pve_generated_stage(ci, s)
    return stages


# Replace the legacy 20-chapter builder (kept above for reference).
_combat_main = _combat_main_40


# Chapter 11-20 names (4 stage names each, in order).
LATE_CHAPTERS = [
    ("赤焰魔域", ["赤焰魔域", "熔火之心", "灰烬王座", "不灭炎狱"]),
    ("苍穹之海", ["苍穹之海", "浮岛遗迹", "风暴之眼", "天穹王座"]),
    ("幽影王陵", ["幽影王陵", "亡者迷宫", "灵魂之井", "冥王神殿"]),
    ("时空裂隙", ["时空裂隙", "逆流回廊", "星轨枢纽", "永恒之门"]),
    ("龙脊山脉", ["龙脊山脉", "龙眠洞穴", "龙魂祭坛", "巨龙王座"]),
    ("深渊海沟", ["深渊海沟", "珊瑚迷城", "海皇宫殿", "深渊主宰"]),
    ("雷电荒原", ["雷电荒原", "雷霆峡谷", "风暴祭坛", "雷神王座"]),
    ("水晶洞窟", ["水晶洞窟", "棱光回廊", "晶核密室", "水晶女王"]),
    ("虚空边境", ["虚空边境", "混沌裂隙", "虚空神殿", "虚空之主"]),
    ("荣耀之巅", ["荣耀之巅", "王者之路", "最终试炼", "最强王座"]),
]

# Enemy roster for generated stages, roughly strongest first.
LATE_ENEMIES = [
    "A_6992_6", "A_6994_6", "A_6997_5", "A_6998_5", "A_6999_5",
    "A_1997_6", "A_6993_5", "A_6996_5", "A_1101_6", "A_1201_6",
    "A_1204_6", "A_1206_6", "A_1209_6", "A_1309_6",
]


def _add_more_stages(stages):
    """Append the 4th stage of chapters 1-10 and all of chapters 11-20."""
    # 4th (elite) stage for the ten hand-written chapters.
    for ci in range(11, 21):
        chapter = "M_%03d" % ci
        last = stages.get(chapter + "_3")
        if last is None:
            continue
        base_lv = 2 + (ci - 11) * 3
        enemies = []
        for j in range(6):
            aid = LATE_ENEMIES[(ci + j) % len(LATE_ENEMIES)]
            enemies.append((aid, base_lv + 3, j % 3, 0.85 if j < 3 else 0.62))
        stages[chapter + "_4"] = _stage(
            "精英试炼", 3, enemies,
            int(last.get("energy", 10)) + 4,
            int(last.get("exp", 20)) * 2,
            int(last.get("gold", 200)) * 2)
    # Chapters 11-20, four stages each.
    for i, (_chapter_name, stage_names) in enumerate(LATE_CHAPTERS):
        ci = 21 + i
        chapter = "M_%03d" % ci
        base_lv = 28 + i * 3
        base_energy = 22 + i * 2
        base_exp = 240 + i * 80
        base_gold = 2400 + i * 800
        for s in range(1, 5):
            count = 2 + s
            enemies = []
            for j in range(count):
                aid = LATE_ENEMIES[(i * 2 + s + j) % len(LATE_ENEMIES)]
                enemies.append((aid, base_lv + (s - 1) * 2 + (j % 2),
                                j % 3, 0.85 if j < 3 else 0.62))
            stages["%s_%d" % (chapter, s)] = _stage(
                stage_names[s - 1], 3, enemies,
                base_energy + s * 2,
                int(base_exp * s * 0.75),
                int(base_gold * s * 0.7))


# --------------------------------------------------------------------------- #
# Activity dungeons (PVE tab 3 / status_pve_activities)
# --------------------------------------------------------------------------- #
# Each activity is a battle_ploy entry; its stages live in cfg.combat_ploy.
# `status_activity` drives the resource icon in ItemPVEmain:
#   1 = gold, 2 = exp, 3 = energy.
ACTIVITY_DUNGEONS = [
    # 2026-10-24 user request: the 活動 tab now holds only 战斗试炼, which
    # contains every old 傷害測試 difficulty.  All other activity dungeons
    # were removed.  Chapter 1's full-star claim grants 1000 點券.
    {
        "id": "W_TRIAL", "name": "战斗试炼", "ulv": 1, "index": 1,
        "status_activity": 1, "cycle": 1440, "duration": 1440,
        "chapter": 1, "pass_reward": 1000,
        "stages": [
            ("傷害測試·三路", 1, 0, 0, 0, 0),
            ("對單測試", 2, 0, 0, 0, 0),
            ("傷害測試·三路·困難", 3, 0, 0, 0, 0),
            ("傷害測試·三路·煉獄", 4, 0, 0, 0, 0),
            ("傷害測試·三路·地獄II", 5, 0, 0, 0, 0),
            ("傷害測試·三路·地獄III", 6, 0, 0, 0, 0),
            ("傷害測試·三路·地獄III·負面", 7, 0, 0, 0, 0),
        ],
        "test_maps": True,
    },
]

# Test-only enemy templates.  They keep the names of gallery heroes #138-#141
# but borrow a normal hero battle resource: the original A_1996..A_1999 cards
# have no battle animation in the client and make the map loader hang.
_TEST_ENEMY_AVATARS = {
    # Killable dummies so on-kill passives (莫德凯撒 悲傷收割) can be tested.
    "A_2996_4": ("A_1001_4", "小經驗果實", 4, 50, 300000),
    "A_2997_6": ("A_1001_4", "大經驗果實", 6, 70, 300000),
    "A_2998_6": ("A_1001_4", "大天使加百列", 6, 70, 300000),
    "A_2999_6": ("A_1001_4", "艾琳教官", 6, 70, 300000),
    # Damage-free dummy used by the status-effect preview stage.
    "A_2995_4": ("A_1001_4", "特效木樁", 4, 50, 1000000000, 0),
    # Hard damage-test dummies: 600k HP (2x the normal 300k).  The normal
    # dummies have 0 defence, so 2x would still be 0; the hard set uses
    # 10,000 physical and magic defence to make the stage meaningfully
    # tougher.  Meta: (src, name, star, lvMax, hp, attack, defence).
    "A_2986_4": ("A_1001_4", "小經驗果實·困難", 4, 50, 600000, 1000, 10000),
    "A_2987_6": ("A_1001_4", "大經驗果實·困難", 6, 70, 600000, 1000, 10000),
    "A_2988_6": ("A_1001_4", "大天使加百列·困難", 6, 70, 600000, 1000, 10000),
    "A_2989_6": ("A_1001_4", "艾琳教官·困難", 6, 70, 600000, 1000, 10000),
    # Inferno damage-test dummies: 1.2M HP, 20,000 physical/magic defence.
    # The stage additionally applies 400 toughness (40% crit resistance)
    # through new_4attrs[3].
    "A_2976_4": ("A_1001_4", "小經驗果實·煉獄", 4, 50, 1200000, 1000, 20000),
    "A_2977_6": ("A_1001_4", "大經驗果實·煉獄", 6, 70, 1200000, 1000, 20000),
    "A_2978_6": ("A_1001_4", "大天使加百列·煉獄", 6, 70, 1200000, 1000, 20000),
    "A_2979_6": ("A_1001_4", "艾琳教官·煉獄", 6, 70, 1200000, 1000, 20000),
    # Hell II / III: 2x and 4x the inferno upper limits (user rule 2026-10-22).
    "A_2966_4": ("A_1001_4", "小經驗果實·地獄II", 4, 50, 2400000, 1000, 40000),
    "A_2967_6": ("A_1001_4", "大經驗果實·地獄II", 6, 70, 2400000, 1000, 40000),
    "A_2968_6": ("A_1001_4", "大天使加百列·地獄II", 6, 70, 2400000, 1000, 40000),
    "A_2969_6": ("A_1001_4", "艾琳教官·地獄II", 6, 70, 2400000, 1000, 40000),
    "A_2956_4": ("A_1001_4", "小經驗果實·地獄III", 4, 50, 4800000, 1000, 80000),
    "A_2957_6": ("A_1001_4", "大經驗果實·地獄III", 6, 70, 4800000, 1000, 80000),
    "A_2958_6": ("A_1001_4", "大天使加百列·地獄III", 6, 70, 4800000, 1000, 80000),
    "A_2959_6": ("A_1001_4", "艾琳教官·地獄III", 6, 70, 4800000, 1000, 80000),
    # 負面測試 (2026-10-23): same Hell III stats, one debuff family each.
    "A_2936_4": ("A_1001_4", "負面測試·虛弱", 4, 50, 4800000, 1000, 80000),
    "A_2937_4": ("A_1001_4", "負面測試·破甲", 4, 50, 4800000, 1000, 80000),
    "A_2938_4": ("A_1001_4", "負面測試·中毒", 4, 50, 4800000, 1000, 80000),
    "A_2939_4": ("A_1001_4", "負面測試·燃燒", 4, 50, 4800000, 1000, 80000),
    "A_2940_4": ("A_1001_4", "負面測試·沉默", 4, 50, 4800000, 1000, 80000),
    "A_2941_4": ("A_1001_4", "負面測試·眩暈", 4, 50, 4800000, 1000, 80000),
    "A_2942_4": ("A_1001_4", "負面測試·詛咒", 4, 50, 4800000, 1000, 80000),
}

# 負面測試: family id -> the single debuff skill it casts on our whole team.
_DEBUFF_TEST_SKILLS = {
    "A_2936_4": "S_TEST_WEAK_1",
    "A_2937_4": "S_TEST_SUNDER_1",
    "A_2938_4": "S_TEST_POISON_1",
    "A_2939_4": "S_TEST_BURN_1",
    "A_2940_4": "S_TEST_SILENCE_1",
    "A_2941_4": "S_TEST_STUN_1",
    "A_2942_4": "S_TEST_EVIL_1",
}


def _debuff_test_skill_cfg():
    """cfg.skill entries for the 負面測試 enemies (whole-team debuffs)."""
    return {
        "S_TEST_WEAK_1": {
            "name": "測試虛弱", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["weak", 0.0, 2, 0.4, 3, "e712"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_SUNDER_1": {
            "name": "測試破甲", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["sunder", 0.0, 2, 0.4, 3, "e715"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_POISON_1": {
            "name": "測試中毒", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["poison", 0.0, 2, 0.3, 3, "e707"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_BURN_1": {
            "name": "測試燃燒", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["burn", 0.1, 3, "e068"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_SILENCE_1": {
            "name": "測試沉默", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["silence", 0.0, 2, 2, "e710"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_STUN_1": {
            "name": "測試眩暈", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["stun", 0.0, 2, 1, "e713"]],
            "skillUp": [0, 0], "info": "",
        },
        "S_TEST_EVIL_1": {
            "name": "測試詛咒", "pl": [0, 3, 9999, 0, 199, 1],
            "skill": [["evil", 2, "e704"]],
            "skillUp": [0, 0], "info": "",
        },
    }


def _test_enemy_avatar_entries():
    out = {}
    for tid, meta in _TEST_ENEMY_AVATARS.items():
        src, name, star, lvmax, hp = meta[:5]
        attack = int(meta[5]) if len(meta) > 5 else 1000
        defence = int(meta[6]) if len(meta) > 6 else 0
        out[tid] = {
            "name": name,
            "res": src,
            "kind": 1,
            # tl: sign/action/damage/leadership/lvMax/expRate/offerExp/
            # offerGold/starUp/sortIndex(-1 hides it from the gallery).
            "tl": [1, 1, 1, 4, lvmax, 1, 0, 0, [], -1],
            # hp0 fixed, hp1 0; attack and both defences configurable.  pl
            # index 4 = physical defence, index 6 = magic defence.
            "pl": [hp, 0, attack, 0, defence, 0, defence, 0, 300, 300,
                   "", "", "E_014", ""],
        }
        # 負面測試 enemies: give each one its own whole-team debuff skill.
        if tid in _DEBUFF_TEST_SKILLS:
            out[tid]["pl"][10] = _DEBUFF_TEST_SKILLS[tid]
    return out


def _pve_boss_avatar_entries(avatars):
    """Enemy-only 6★ copies of the advanced gatekeeper heroes.

    The real hero entries keep their normal player balance.  These copies
    (A_8022_6 …) reuse the hero's art/name/skills but use a fixed boss stat
    profile (HP 20000+2200/level, ATK 1300+150/level, defence 1200+40/level).
    That makes every chapter's gatekeepers roughly 2.5× a wild monster at
    the same level regardless of which hero family guards the stage, so the
    stage-4 difficulty rises smoothly with the chapter.  tl[9] = -1 keeps
    them out of the gallery.
    """
    out = {}
    for fam in PVE_ADVANCED_HEROES:
        src = avatars.get(fam + "_6") or avatars.get(fam + "_5")
        if not isinstance(src, dict):
            continue
        bid = _pve_boss_family(fam) + "_6"
        entry = dict(src)
        pl = list(src.get("pl") or [])
        while len(pl) < 14:
            pl.append(0)
        # Fixed boss profile: hero skills/art, but the stats no longer vary
        # with the gatekeeper family, so the stage-4 curve is predictable.
        pl[0], pl[1] = 20000, 2200
        pl[2], pl[3] = 1300, 150
        pl[4], pl[5] = 1200, 40
        pl[6], pl[7] = 1200, 40
        entry["pl"] = pl
        entry["res"] = src.get("res", fam + "_6")
        tl = list(src.get("tl") or [1, 1, 1, 4, 100, 1, 100, 100, [], -1])
        while len(tl) < 11:
            tl.append(0)
        tl[9] = -1
        entry["tl"] = tl
        out[bid] = entry
    return out


def _activity_combat():
    """cfg.combat_ploy: battle maps for every activity stage."""
    out = {}
    for act in ACTIVITY_DUNGEONS:
        if act.get("test_maps"):
            makers = [
                _test_stage_map, _preview_stage_map, _test_hard_stage_map,
                _test_inferno_stage_map, _test_hell2_stage_map,
                _test_hell3_stage_map, _test_debuff_stage_map,
            ]
            for idx, maker in enumerate(makers, 1):
                stage = maker()
                stage["name"] = act["stages"][idx - 1][0]
                stage["energy"] = 0
                stage["exp"] = TRIAL_STAGE_EXP[idx - 1] \
                    if idx <= len(TRIAL_STAGE_EXP) else 100
                stage["gold"] = 0
                # Every clear pays 點券; the settlement panel reads win_gift.
                stage["win_gift"] = {"coin": 100}
                stage["no_drop"] = True
                stage["limit"] = [9999, 9999]
                for enemy in stage.get("team2") or []:
                    enemy[6] = 0      # dropRate
                    enemy[8] = ""     # dropId
                out["%s_%d" % (act["id"], idx)] = stage
            continue
        for idx, (name, n, energy, exp, gold, _x) in enumerate(
                act["stages"], 1):
            count = min(6, 3 + idx)
            enemies = []
            for j in range(count):
                aid = _pve_sanitize_units(
                    [act["enemies"][(idx + j) % len(act["enemies"])]])[0]
                enemies.append((aid, 6 + idx * 4 + j // 3, j % 3,
                                0.85 if j < 3 else 0.62))
            stage = _stage(name, 3, enemies, energy, exp, gold)
            stage["limit"] = [9999, 9999]
            if act.get("equip_drop") and idx <= len(act["equip_drop"]):
                stage["equip_drop"] = act["equip_drop"][idx - 1]
            if act.get("energy_reward") and idx <= len(act["energy_reward"]):
                stage["energy_reward"] = act["energy_reward"][idx - 1]
            if act.get("mat_reward") and idx <= len(act["mat_reward"]):
                stage["mat_reward"] = act["mat_reward"][idx - 1]
            out["%s_%d" % (act["id"], idx)] = stage
    return out


def _battle_ploy_cfg():
    """cfg.battle_ploy: activity-dungeon definitions for PVE tab 3."""
    start = datetime.datetime.utcnow() - datetime.timedelta(days=1)
    end = datetime.datetime.utcnow() + datetime.timedelta(days=3650)
    out = {}
    for act in ACTIVITY_DUNGEONS:
        out[act["id"]] = {
            "name": act["name"],
            "ulv": act["ulv"],
            "index": act["index"],
            "combat": len(act["stages"]),
            "state": 0,
            "status_activity": act["status_activity"],
            "start_time": start,
            "end_time": end,
            "cycle": act["cycle"],
            "duration": act["duration"],
            # Full-star claim reward (點券).  Chapter 1 = 1000; later
            # chapters scale with `chapter`.
            "chapter": int(act.get("chapter", 1)),
            "pass_reward": int(act.get("pass_reward",
                                       1000 * int(act.get("chapter", 1)))),
        }
    return out


_CH_CN_DIGITS = ["零", "一", "二", "三", "四", "五", "六", "七", "八", "九"]


def _cn_number(n):
    """1..99 -> Chinese numeral (一, 十, 十一, 二十, 四十 …)."""
    if n < 10:
        return _CH_CN_DIGITS[n]
    tens, ones = divmod(n, 10)
    head = "" if tens == 1 else _CH_CN_DIGITS[tens]
    return head + "十" + ("" if ones == 0 else _CH_CN_DIGITS[ones])


def _battle_main_cfg():
    """cfg.battle_main: 40 chapters, 4 stages each (chapter 1 has trials)."""
    out = {}
    for i in range(PVE_CHAPTER_COUNT):
        # Keep every chapter reachable for the level-50 account: chapter 40
        # requires level 40.
        ulv = min(50, 1 + i)
        out["M_%03d" % (PVE_FIRST_CHAPTER + i)] = {
            "name": "第%s章" % _cn_number(i + 1),
            "ulv": ulv,
            # indexID_s sorts descending so the newest chapter is selected.
            "indexID_s": PVE_CHAPTER_COUNT - i,
            "combat": PVE_STAGES_PER_CHAPTER,
            "story": [],
        }
    return out


def _effect_table():
    """Map cfg.effect ids to the DragonBones animations embedded in the client.

    The SWF ships an ``effectDB`` skeleton (armatures ``effect/e001`` …
    ``effect/e019`` for the skill effect sets E_001…E_019, plus e020+ for
    various one-off effects).  ``EffectManager.getData()`` returns the stored
    object as-is and DisplayTools treats it as an effect descriptor:

      id  - animation name (lower-case "e…" → DragonBonesSprite)
      b   - projectile descriptor used by addBullet() when it flies
      h   - impact descriptor played on the victim by Avatar.injured()
      sp  - projectile speed in px/s (client default 800)
      sc  - uniform scale

    Everything the client can request must exist: an undefined entry makes
    ``attrs.a1 = avatar`` throw #1010 at cast time.  Keys we intentionally
    leave blank (full-screen intros, lane banners) stay empty objects — the
    client silently skips them.
    """
    fx = {
        # cast flash over the caster when a skill fires.
        # ``t`` is mandatory here: e020's animation is authored with loop="0"
        # (DragonBones' "infinite") so it never emits "complete" and would
        # otherwise leave a looping flash on the ground after every cast.
        # Hero-skill / leader-skill activation flashes.  e001/e002 are the
        # dedicated one-shot cast effects (they finish before the actions).
        "SKILL0_PRE_EFF": {"id": "e001", "sc": 1,
                            "s": {"id": "skill0", "v": 0.30}},
        "SKILL1_PRE_EFF": {"id": "e002", "sc": 1,
                            "s": {"id": "skill1", "v": 0.35}},
        # backfire projectile (reflect / avenge buffs)
        "BACK_BUL": {"id": "e008", "sp": 900,
                     "b": {"id": "e008", "sc": 0.5}},
        # persistent / one-shot status effects
        "POISON_EFF": {"id": "e019", "sc": 0.7},
        "BURN_EFF": {"id": "e019", "sc": 0.7},
        "BLESS_EFF": {"id": "e010", "sc": 0.7},
        "SUCK_EFF": {"id": "e011", "sc": 0.7},
        "SUMMON_EFF": {"id": "e015", "sc": 0.8},
        "ADD_AVATAR_EFF": {"id": "e027", "sc": 0.8},
        "RANDOM_AVATAR_EFF": {"id": "e028", "sc": 0.8},
        "DEAD_MODE_EFF": {"id": "e029", "sc": 0.9},
        # e030 is also loop="0" in the skeleton; it is spawned 10x as a burst
        "DEAD_MODE_START_EFF": {"id": "e030", "sc": 0.9, "t": 0.3},
        "GANK": {"id": "e066", "sc": 0.8},
        "TAUNT_HIT_EFF": {"id": "e067", "sc": 0.7},
        # SIGN is a deliberate persistent sparkle on the sign-in plant
        "SIGN": {"id": "e068", "sc": 0.8},
        "RE_LINE_IN_EFF_1": {"id": "e069", "sc": 0.7},
        "RE_LINE_IN_EFF_2": {"id": "e070", "sc": 0.7, "t": 0.7},
        "RE_LINE_OUT_EFF_1": {"id": "e069", "sc": 0.7},
        "RE_LINE_OUT_EFF_2": {"id": "e070", "sc": 0.7, "t": 0.7},
        "RE_LINE_IN_EFF_": {"id": "e069", "sc": 0.7},
        "RE_LINE_OUT_EFF_": {"id": "e069", "sc": 0.7},
        # full-screen / lane-banner effects we don't reconstruct yet
        "OPENING_ANIMATION": {},
        "LINESIGN": {},
        "LINESIGN1": {},
        "LINESIGN2": {},
        "weather": {},
    }
    # Buff.displayObject() looks up cfg.effect[<buff type>] directly.  Without
    # these keys every positive/negative status was applied silently (the
    # client got null from newDisplayObject and showed nothing).
    fx.update({
        # Original persistent status armatures (e7xx) extracted from the
        # single-player 1.0.2 build's cfg.effect.  They are authored with
        # loop="0" so they stay on the avatar until the Buff is removed.
        # 2026-10-20: distinct sound per buff type (user request).  The
        # original table reused `cure` for most positives; E_9010..E_9023 are
        # standalone one-shot cues already shipped with the client audio.
        # 2026-10-20: the original single-player cfg.effect is authoritative
        # for the effect-set sounds: E_010 (holy/heal) -> E_9010 and
        # E_001 (shield/protection) -> E_9004.  The heal was previously
        # playing the generic hit cue and the shield buff E_9012, which made
        # the two sound swapped in game.
        "purify": {"id": "e708", "sc": 1.0, "t": 0, "loop": True,
                    "s": {"id": "E_9012", "v": 0.40}},
        "bless": {"id": "e701", "sc": 1.0, "t": 0, "loop": True,
                   "s": {"id": "E_9011", "v": 0.40}},
        "shield": {"id": "e709", "sc": 1.0, "t": 0, "loop": True,
                    "s": {"id": "E_9004", "v": 0.45}},
        "steel": {"id": "e711", "sc": 1.0, "t": 0, "loop": True,
                   "s": {"id": "E_9013", "v": 0.40}},
        "strong": {"id": "e703", "sc": 1.0, "t": 0, "loop": True,
                    "s": {"id": "E_9014", "v": 0.40}},
        "taunt": {"id": "e716", "sc": 1.0, "t": 0, "loop": True,
                   "s": {"id": "E_9015", "v": 0.40}},
        "poison": {"id": "e707", "sc": 1.0, "t": 0, "loop": True,
                    "s": {"id": "E_9007", "v": 0.35}},
        "burn": {"id": "e068", "sc": 1.0, "t": 0, "loop": True,
                  "s": {"id": "E_9008", "v": 0.40}},
        "stun": {"id": "e713", "sc": 1.0, "t": 0, "loop": True,
                  "s": {"id": "stun", "v": 0.45}},
        "silence": {"id": "e710", "sc": 1.0, "t": 0, "loop": True,
                     "s": {"id": "E_9003", "v": 0.40}},
        "weak": {"id": "e712", "sc": 1.0, "t": 0, "loop": True,
                  "s": {"id": "E_9002", "v": 0.40}},
        "sunder": {"id": "e715", "sc": 1.0, "t": 0, "loop": True,
                    "s": {"id": "E_9005", "v": 0.40}},
        "evil": {"id": "e704", "sc": 1.0, "t": 0, "loop": True,
                  "s": {"id": "E_9006", "v": 0.35}},
        "hitup": {"id": "e706", "sc": 1.0, "t": 0, "loop": True,
                   "s": {"id": "E_9016", "v": 0.35}},
        "critup": {"id": "e705", "sc": 1, "t": 0, "loop": True,
                    "s": {"id": "E_9017", "v": 0.35}},
        "critdmgup": {"id": "e705", "sc": 1, "t": 0, "loop": True,
                       "s": {"id": "E_9017", "v": 0.35}},
        "toughup": {"id": "e717", "sc": 1.0, "t": 0, "loop": True,
                     "s": {"id": "E_9018", "v": 0.35}},
        # No dedicated persistent armature in the extracted effect table;
        # the client draws these with its procedural BuffVisual fallback.
        "fleeup": {"fallback": True, "s": {"id": "E_9019", "v": 0.35}},
        "asuck": {"fallback": True, "s": {"id": "E_9020", "v": 0.35}},
        "back": {"fallback": True, "s": {"id": "E_9021", "v": 0.35}},
        "avenge": {"fallback": True, "s": {"id": "E_9022", "v": 0.35}},
        "summon": {"fallback": True, "s": {"id": "E_9023", "v": 0.35}},
    })
    # Raw armature ids, used by the M_011_6 "狀態特效預覽" stage so the
    # effect-to-buff mapping can be inspected in-game.
    for _i in (list(range(1, 35)) + [66, 67, 68, 69, 70]
               + list(range(201, 207)) + list(range(301, 309))
               + list(range(501, 512))):
        fx["e%03d" % _i] = {"id": "e%03d" % _i, "sc": 1}
    # Skill effect sets.  Basic attacks also use avatarData.effectSet, so the
    # same descriptor gives every auto-attack a visible projectile and impact.
    # Sound cues follow the original single-player cfg.effect arrays:
    #   E_001->E_9004, E_002->E_9005, ..., E_010->E_9010 (heal/holy), ...
    # Using one generic hit cue here made the heal (E_010) and shield (E_001)
    # sound identical/swapped in game.
    _effect_sound = {
        1: "E_9004", 2: "E_9005", 3: "E_9006", 4: "E_9007",
        5: "E_9008", 6: "E_9003", 7: "E_9003", 9: "E_9009",
        10: "E_9010", 11: "E_9011", 12: "E_9012", 13: "E_9013",
        14: "E_9014", 15: "E_9015", 16: "E_9016", 17: "E_9017",
        18: "E_9018", 19: "E_9019",
    }
    for i in range(1, 20):
        eid = "e%03d" % i
        # Per the in-game effect list: E_001 is used for shield/protection,
        # E_005 for control (stun) and E_010 for holy light damage.  Their
        # original armature ids are cast/hit flashes, not the matching ones.
        if i == 1:
            eid = "e019"       # 自身防护类技能释放
        elif i == 5:
            eid = "e022"       # 符文禁锢等控制类
        elif i == 10:
            eid = "e028"       # 光芒闪耀
        fx["E_%03d" % i] = {
            "id": eid,
            "sp": 800,
            "b": {"id": eid, "sc": 0.55},
            "h": {"id": eid, "sc": 0.65,
                  "s": {"id": _effect_sound.get(i, "E_9002"), "v": 0.30}},
        }
    # 2026-10-20 鋼鐵俠提摩 / 鋼鐵蘑菇: use the original one-shot armatures
    # directly (EFFECT_IDS.md) instead of a generic E_xxx set.
    #   e202  左→右細小光線（雷射）
    #   e026  回血
    #   e013  召喚物腳下法陣
    #   e305/e306  英雄瞬移出發／落地
    #   e508  子彈
    # The raw loop above created bare {id, sc} entries; these richer
    # descriptors add the projectile/impact data that attackAimList needs.
    fx.update({
        "e202": {"id": "e202", "sp": 1600,
                 "b": {"id": "e202", "sc": 0.8},
                 "h": {"id": "e202", "sc": 0.8,
                       "s": {"id": "E_9009", "v": 0.30}}},
        # 2026-10-20: the e508 bullet armature is authored with loop="0" and
        # previously stayed on the victim after 鋼鐵急射 (visible bullet-effect
        # residue).  Give the impact a short lifetime; addBullet already
        # clears the flying projectile itself via its flight tween.
        "e508": {"id": "e508", "sp": 1400,
                 "b": {"id": "e508", "sc": 0.7},
                 "h": {"id": "e508", "sc": 0.7, "t": 0.35,
                       "s": {"id": "E_9005", "v": 0.30}}},
        "e026": {"id": "e026", "sc": 0.8,
                 "s": {"id": "E_9010", "v": 0.40}},
        "e013": {"id": "e013", "sc": 0.8,
                 "s": {"id": "E_9023", "v": 0.35}},
        "e305": {"id": "e305", "sc": 0.8},
        "e306": {"id": "e306", "sc": 0.8},
        # 2026-10-22 艾尼維亞 ice shard: e501 is the original left→right
        # blue magic projectile; e003 is the blue magic impact.
        # 冰霜風暴 shards are +50% size (user request); the passive's single
        # 無垢冰稜 uses e501_big at +100% of the original size.
        "e501": {"id": "e501", "sp": 1300, "sc": 1.5,
                 "b": {"id": "e501", "sc": 1.125},
                 "h": {"id": "e003", "sc": 1.2,
                       "s": {"id": "E_9009", "v": 0.30}}},
        "e501_big": {"id": "e501", "sp": 1300, "sc": 2.0,
                     "b": {"id": "e501", "sc": 1.5},
                     "h": {"id": "e003", "sc": 1.6,
                           "s": {"id": "E_9009", "v": 0.30}}},
        # 2026-10-22 費德提克:
        #   e_laser    掠奪的細長筆直雷射：the beam itself is drawn by
        #              SkillSet.playBeamTo (white core + cyan glow Quad,
        #              caster→target), so this descriptor only carries the
        #              hit spark and the Iron Man Teemo normal-attack sound
        #              E_9019.  No bullet part: the e202 armature read as
        #              lightning, not a laser.
        #   e_darkwave 冥吞的黑暗魔法飛彈（e509）+ 暗影受擊（e069）。
        #   e_darkbolt 嗜厄的黑暗魔法彈（e509），命中播放詛咒音效。
        "e_laser": {"id": "e009", "sp": 2400,
                    "h": {"id": "e009", "sc": 0.7,
                          "s": {"id": "E_9019", "v": 0.30}}},
        "e_darkwave": {"id": "e509", "sp": 1300,
                       "b": {"id": "e509", "sc": 0.9},
                       "h": {"id": "e069", "sc": 0.9,
                             "s": {"id": "E_9006", "v": 0.35}}},
        "e_darkbolt": {"id": "e509", "sp": 1500,
                       "b": {"id": "e509", "sc": 1.0},
                       "h": {"id": "e069", "sc": 0.8,
                             "s": {"id": "E_9006", "v": 0.30}}},
        # 2026-10-23 圖奇 腐爛投擲: keep the e009 magic armature but make
        # the projectile/impact noticeably bigger (1.6x/1.8x).  The hit cue
        # is E_9006 (2026-10-23 second pass; E_9008 was the previous pick,
        # E_9009 the default E_009 set).
        "e_rot": {"id": "e009", "sp": 900, "sc": 1.8,
                  "b": {"id": "e009", "sc": 1.6},
                  "h": {"id": "e009", "sc": 1.8,
                        "s": {"id": "E_9006", "v": 0.35}}},
        # 2026-10-24 伊莉絲 神經毒素: the original E_009 magic projectile and
        # impact, scaled up by 100% (bullet 0.55 -> 1.1, hit 0.65 -> 1.3).
        "E_009_BIG": {"id": "e009", "sp": 800, "sc": 2,
                      "b": {"id": "e009", "sc": 1.1},
                      "h": {"id": "e009", "sc": 1.3,
                            "s": {"id": "E_9009", "v": 0.30}}},
        # 2026-10-24 地獄隕落: 火球飛彈（e507 左→右火球）+ 爆炸受擊 e010,
        # 命中播放引燃音效。attackAimList 讀 descriptor 的 b 部分自動發射
        # 彈道並在飛行結束後結算傷害。
        "e_hellfire": {"id": "e507", "sp": 850, "sc": 1.1,
                       "b": {"id": "e507", "sc": 0.95},
                       "h": {"id": "e010", "sc": 1.0,
                             "s": {"id": "E_9008", "v": 0.35}}},
        # 2026-10-24 神技：狙殺 — 箭矢飛彈 + 中彈火花.
        "e_snipe": {"id": "e505", "sp": 2000, "sc": 1.0,
                    "b": {"id": "e505", "sc": 1.0},
                    "h": {"id": "e005", "sc": 1.0,
                          "s": {"id": "E_9004", "v": 0.30}}},
        # 神技：突襲 — 近身三段斬擊（e006 多段斬擊）。
        "e_phantom": {"id": "e006",
                      "h": {"id": "e006", "sc": 1.0,
                            "s": {"id": "E_9004", "v": 0.30}}},
        # 神技：鐵腕 — 護盾撞擊的中彈火花.
        "e_shieldhit": {"id": "e005",
                        "h": {"id": "e005", "sc": 1.2,
                              "s": {"id": "E_9004", "v": 0.35}}},
        # 魔技：獻祭 — 暗影彈（e509）+ 暗影受擊（e069）.
        "e_bloodpact": {"id": "e509", "sp": 1200, "sc": 1.0,
                        "b": {"id": "e509", "sc": 1.0},
                        "h": {"id": "e069", "sc": 1.0,
                              "s": {"id": "E_9006", "v": 0.35}}},
        # 2026-10-24 毒性爆發: extra poison-burst flash played on every
        # detonated enemy (no sound — the damage descriptor already cues
        # E_9009).
        "TOX_HIT_EFF": {"id": "e019", "sc": 1.3},
    })
    return fx


# Swallow-panel consumables that are not ordinary EXP food.  The client's
# Avatar.isSwallowProtect() rejects any material whose offerGold/offerExp
# ratio exceeds 1.5, so these families get a low offerGold below.  Their
# effects are applied by family id rather than the generic EXP path.
SKILL_COOKIE_GAIN = {"A_2107": 100, "A_6992": 500}
LOVE_POTION_FAMILY = "A_6993"
# 250号魔法药水：4★ 100 / 5★ 300 / 6★ 600 好感度。  6★ must be the
# strongest; the old family-wide 100 made every star identical.
LOVE_POTION_GAIN = {
    # 2026-10-25 user: magic potion effect is too strong, halve it.
    "A_6993_4": 50,
    "A_6993_5": 150,
    "A_6993_6": 300,
}
SWALLOW_SPECIAL_FAMILIES = set(SKILL_COOKIE_GAIN) | {LOVE_POTION_FAMILY}

# 2026-10-21 experience crops: gallery 145-150, 165-192, 252-255 all count
# as food and give 50000 flat EXP when swallowed (the client's legal cap).
EXP_CROP_FAMILIES = (
    {"A_2004", "A_2005", "A_2006", "A_2008", "A_2009", "A_2010",
     "A_2108", "A_6995", "A_6996", "A_6997", "A_6998"}
    | {"A_%04d" % n for n in range(2300, 2327)}
)

# 2026-10-21 skill-level materials: 164 (A_2107_4) 10%, 5★249
# (A_6992_5) 20%, 6★249 (A_6992_6) 40%.  The client shows the summed
# percentage in the 技能點 field; the server rolls the same value.
SKILL_UP_CHANCE = {
    "A_2107_4": 10,
    "A_6992_5": 20,
    "A_6992_6": 40,
}

# 2026-10-21 star-up material rules (gallery tile numbers):
#   225 A_6003_1 石頭精靈, 226 A_6004_2 聚元, 232 A_6022_3 破障,
#   244 A_6076_4 启迪, 243 A_6075_5 脱缚, 251 A_6994_6 渡厄.
# Each hero star consumes exactly ONE matching material; the phase gate is
# enforced by phase_config (3★ 1阶, 4★/5★ 2阶, 6★ 3阶).
STARUP_MATERIALS = {
    1: "A_6003_1",
    2: "A_6004_2",
    3: "A_6022_3",
    4: "A_6076_4",
    5: "A_6075_5",
    6: "A_6994_6",
}
STARUP_MIN_PHASE = {1: 0, 2: 0, 3: 1, 4: 2, 5: 2, 6: 3}

# 2026-10-25: every gameplay soul-stone (魂石) reward is multiplied by this.
# Applied to expedition decompose, PVE clears, arena and cross-server PVP.
DN_STONE_REWARD_RATE = 10

# 2026-10-21 極限突破 materials (gallery tile 256, A_6999):
#   3★ 靈眷秘寶 10%, 4★ 天眷秘寶 15%, 5★ 神眷秘寶 20%.
# Up to 5 materials may be fed at once; the rates add up (cap 100%).
LIMIT_BREAK_RATES = {
    "A_6999_3": 0.10,
    "A_6999_4": 0.15,
    "A_6999_5": 0.20,
}
LIMIT_BREAK_MAX_MATS = 5
# Per-star display names override the family-wide UNIT_NAMES entry.
STAR_MATERIAL_NAMES = {
    "A_6999_3": "靈眷秘寶",
    "A_6999_4": "天眷秘寶",
    "A_6999_5": "神眷秘寶",
    # 2026-10-23: 250號魔法藥水按星級規範命名（4/5/6★ = 小/中/大），
    # 249號技能餅乾-中 = 5★（20%）。
    "A_6993_4": "魔法藥水-小",
    "A_6993_5": "魔法藥水-中",
    "A_6993_6": "魔法藥水-大",
    "A_6992_5": "技能餅乾-中",
}

# 2026-10-21 leadership (统御) redesign.  Hero tiers follow the gallery
# positions the user supplied (1-141): 1-21 & 127-137 novice, the listed
# 22-32/37/... positions advanced, everything else high.  Values are the
# 0-阶 cost per star; each 阶 adds lead_phase (+1 for 2-5★, +2 for 6★).
LEADERSHIP_TABLE = {
    "novice":   {2: 2,  3: 4,  4: 7,  5: 11, 6: 15, 7: 25},
    "advanced": {2: 13, 3: 15, 4: 18, 5: 22, 6: 26, 7: 36},
    "high":     {2: 35, 3: 37, 4: 40, 5: 44, 6: 48, 7: 58},
}
LEADERSHIP_NOVICE_POS = set(range(1, 22)) | set(range(127, 142))
# User correction 2026-10-21: gallery 108 (A_1212 粽香少女) is a high-tier
# hero, not advanced.  Advanced/VIP draw pools and the third passive skill
# all follow this same map.
LEADERSHIP_ADVANCED_POS = set(
    list(range(22, 33)) + [37, 39, 40, 41, 42, 49, 51, 52, 53, 57,
                           59, 60, 62, 67, 68, 75])


def _lead_tier(pos):
    if pos in LEADERSHIP_NOVICE_POS:
        return "novice"
    if pos in LEADERSHIP_ADVANCED_POS:
        return "advanced"
    return "high"


_GALLERY_RANK_CACHE = None
_GALLERY_TIER_CACHE = None


def _gallery_display_ranks():
    """1-based gallery rank -> family base, mirroring PanelHelpAvatar.

    ``HERO_NAMES`` insertion order is not the gallery order: A_12xx skin
    cards sit at 104-112 there, while their real tl[9] tiles sort at 97-108.
    Everything tier-related (stats, skills, passives, altar pools) must use
    this actual ranking.
    """
    global _GALLERY_RANK_CACHE
    if _GALLERY_RANK_CACHE is not None:
        return _GALLERY_RANK_CACHE
    displays = {}
    for aid, meta in AVATAR_CATALOG.items():
        if not aid.startswith("A_1"):
            continue
        try:
            base, star_s = aid.rsplit("_", 1)
            star = int(star_s)
            int(base.split("_")[1])
        except (ValueError, IndexError):
            continue
        if int(meta.get("kind", 1) or 0) != 1:
            continue
        score = (1 if meta.get("res") == aid else 0, star)
        if base not in displays or score > displays[base][0]:
            displays[base] = (score, aid)
    rows = []
    for base, (_score, _aid) in displays.items():
        if base in GALLERY_HIDDEN:
            continue
        try:
            fam = int(base.split("_")[1])
        except ValueError:
            continue
        rows.append((GALLERY_SORT_OVERRIDES.get(base, fam - 1000), base))
    rows.sort()
    _GALLERY_RANK_CACHE = {
        rank: base for rank, (_pos, base) in enumerate(rows, 1)
    }
    return _GALLERY_RANK_CACHE


def _gallery_tier_map():
    """family base -> novice / advanced / high, using actual gallery rank."""
    global _GALLERY_TIER_CACHE
    if _GALLERY_TIER_CACHE is not None:
        return _GALLERY_TIER_CACHE
    _GALLERY_TIER_CACHE = {
        base: _lead_tier(rank)
        for rank, base in _gallery_display_ranks().items()
    }
    return _GALLERY_TIER_CACHE


# 2026-10-23 遠征（分解）積分（用戶最終數值）:
#   只有「高級」英雄返還活動積分；新手/進階英雄分解不給積分，
#   避免用低階卡刷積分換高級英雄。
#   高級英雄基礎分（0階）: 4★45 / 5★90 / 6★360 / 7★2880
#   每升一階翻倍: 5★ 90/180/360、6★ 360/720/1440/2880、7★ 2880。
EXPEDITION_POINTS_BASE = {
    4: 45,
    5: 90,
    6: 360,
    7: 2880,
}


def _expedition_points(key, inst):
    aid = str(key).split("|")[0]
    if not aid.startswith("A_1"):
        return 0
    try:
        fam, star_s = aid.rsplit("_", 1)
        star = int(star_s)
    except (ValueError, IndexError):
        return 0
    if star < 4:
        return 0
    # 只有高級英雄給積分；新手/進階返還 0。
    if _gallery_tier_map().get(fam, "high") != "high":
        return 0
    base = EXPEDITION_POINTS_BASE.get(star, 0)
    try:
        phase = int((inst or {}).get("phase", 0) or 0)
    except (TypeError, ValueError):
        phase = 0
    return base * (2 ** max(0, phase))


def _hero_family(aid):
    """A_1079_7|2203 -> A_1079; None for non-hero cards (materials/potions)."""
    if not isinstance(aid, str):
        return None
    base = aid.split("|")[0]
    if not base.startswith("A_1"):
        return None
    i = base.rfind("_")
    return base[:i] if i > 0 else base


def _dedupe_team_row(row):
    """同一隊伍不能上陣重複英雄: keep the first card of each hero family.

    Materials (potions etc.) are not heroes, so several copies may share a
    team row.  Empty slots (None/"") are left untouched.
    """
    seen = set()
    for i, key in enumerate(list(row)):
        fam = _hero_family(key)
        if fam is None:
            continue
        if fam in seen:
            row[i] = None
        else:
            seen.add(fam)
    return row


# 2026-10-25: usage descriptions for material cards (shown in the avatar
# detail text box).  Star-up materials are keyed by family; cookies,
# potions and 神眷秘寶 by exact star id.
_MATERIAL_DESC_BY_FAMILY = {
    "A_6003": "升星材料：1★英雄升2★時使用。",
    "A_6004": "升星材料：2★英雄升3★時使用。",
    "A_6022": "升星材料：3★英雄升4★時使用。",
    "A_6076": "升星材料：4★英雄升5★時使用。",
    "A_6075": "升星材料：5★英雄升6★時使用。",
    "A_6994": "升星材料：6★英雄升7★時使用。",
}
_MATERIAL_DESC_BY_AID = {
    "A_2107_4": "吞噬時有 10% 機率使英雄技能等級 +1（上限10級）。",
    "A_6992_5": "吞噬時有 20% 機率使英雄技能等級 +1（上限10級）。",
    "A_6992_6": "吞噬時有 40% 機率使英雄技能等級 +1（上限10級）。",
    "A_6993_4": "吞噬時增加 50 點好感度；好感等級可降低英雄統御值。",
    "A_6993_5": "吞噬時增加 150 點好感度；好感等級可降低英雄統御值。",
    "A_6993_6": "吞噬時增加 300 點好感度；好感等級可降低英雄統御值。",
    "A_6999_3": "極限突破材料：吞噬時每顆提供 10% 突破機率（最多5顆，機率相加，上限100%）。",
    "A_6999_4": "極限突破材料：吞噬時每顆提供 15% 突破機率（最多5顆，機率相加，上限100%）。",
    "A_6999_5": "極限突破材料：吞噬時每顆提供 20% 突破機率（最多5顆，機率相加，上限100%）。",
}


def _material_desc(base, star, aid=None):
    """Return the usage description for a material card, else ""."""
    if aid in _MATERIAL_DESC_BY_AID:
        return _MATERIAL_DESC_BY_AID[aid]
    if base in _MATERIAL_DESC_BY_FAMILY:
        return _MATERIAL_DESC_BY_FAMILY[base]
    if base in EXP_CROP_FAMILIES or base in EXP_MATERIAL_FAMILIES:
        return "吞噬時提供 50,000 經驗。"
    return ""


def _avatar_entry(aid, meta):
    """Expand avatar_catalog metadata into the client's AvatarData shape.

    AvatarData reads tl=[signType, actionType, damageType, leadership,
    lvMax, expRate, offerExp, offerGold, starUp] and pl=[hp0, hp1, ap0, ap1,
    d10, d11, d20, d21, speed, range, skill0, skill1, effectSet].
    """
    star = int(meta.get("star", 4))
    base = aid.rsplit("_", 1)[0]
    arch = ARCH_OVERRIDES.get(base, meta.get("arch", "attack"))
    kind = int(meta.get("kind", 1))
    scale = 1.0 if kind == 1 else 0.55
    if arch == "tank":
        sign, action, dmg = 2, 1, 1
        hp0, hp1 = 760 + 75 * star, 58 + 5 * star
        ap0, ap1 = 170 + 16 * star, 10 + 1.5 * star
        d0, d1, spd, rng = 140 + 5 * star, 4, 330, 300
        skill0, skill1, eff = "S_1010_1", "S_1011_1", "E_009"
    elif arch == "assist":
        # actionType 3 is the client's support/healer branch: healers don't
        # block a line from being lost, can't be missed, and get the
        # heroFrame3 UI.  Using 2 made them behave like ordinary ranged.
        sign, action, dmg = 3, 3, 2
        hp0, hp1 = 600 + 60 * star, 48 + 4.5 * star
        ap0, ap1 = 230 + 22 * star, 14 + 2 * star
        d0, d1, spd, rng = 105 + 3 * star, 3, 390, 250
        skill0, skill1, eff = "S_1009_1", "S_1004_1", "E_010"
    elif arch == "mage":
        # Backline magic attacker: actionType 1 makes Avatar.newAvatarRes()
        # use getAvatarIcon() (the card) instead of the raw A_xxxx_6 hero art,
        # while damageType 2 keeps magic class advantage/skill scaling.
        sign, action, dmg = 1, 1, 2
        hp0, hp1 = 560 + 55 * star, 42 + 4 * star
        ap0, ap1 = 280 + 30 * star, 17 + 2.2 * star
        d0, d1, spd, rng = 120 + 4 * star, 4, 420, 230
        skill0, skill1, eff = "S_1012_1", "S_1002_1", "E_008"
    else:
        sign, action, dmg = 1, 1, 1
        hp0, hp1 = 560 + 55 * star, 42 + 4 * star
        ap0, ap1 = 280 + 30 * star, 17 + 2.2 * star
        d0, d1, spd, rng = 120 + 4 * star, 4, 420, 230
        skill0, skill1, eff = "S_1012_1", "S_1002_1", "E_008"
    # A few cards need a client actionType that differs from their stat
    # archetype (e.g. A_1013 is an assist but must draw its card icon in
    # battle instead of the large standing art).
    action = ACTION_OVERRIDES.get(base, action)
    # 2026-10-24: the client treats actionType 3 (堅守/stand) as a
    # non-team unit — ItemAvatarForTeam rejects it with "該英雄已在隊伍中"
    # (message 90511), so every assist-role hero was impossible to place in
    # the normal team.  Heroes must be 1 (forward) or 2 (ranged); keep 3
    # only for monsters/buildings.
    if kind == 1 and action == 3:
        action = 2
    # Non-hero units keep the old per-star curve.  Gallery heroes use the
    # three-tier 5-star templates; their damage type also decides how the
    # single defence value is split into physical/magic defence.
    d20, d21 = d0, d1
    # 2026-10-24 v3: 40-chapter PVE difficulty.  All wild monsters share one
    # stat profile and all buildings a slightly tankier one.  This removes the
    # per-family HP variance that made some chapters easier than the previous
    # one, so the total enemy HP rises strictly with the chapter level.
    # Test dummies use A_29xx hero entries and are not touched here.
    if base in PVE_WILD_MONSTERS:
        hp0, hp1 = 8000, 1200
        ap0, ap1 = 600, 100
        d0 = d20 = 700
        d1 = d21 = 30
    elif base in PVE_BUILDINGS:
        hp0, hp1 = 9000, 1300
        ap0, ap1 = 700, 110
        d0 = d20 = 900
        d1 = d21 = 35
    hero = (hero_stats(base, star, arch, _gallery_tier_map().get(base))
            if (kind == 1 and hero_stats) else None)
    if kind == 1:
        # Give every hero family its own pair of skills and a small,
        # deterministic stat spread instead of one of three fixed templates.
        try:
            fam = int(aid.split("_")[1])
        except (IndexError, ValueError):
            fam = 1
        pools = {
            "attack": ["S_1000_1", "S_1001_1", "S_1003_1", "S_1005_1",
                       "S_1006_1", "S_1007_1", "S_1008_1", "S_1012_1",
                       "S_1013_1", "S_1014_1", "S_1016_1", "S_1017_1",
                       "S_1018_1"],
            "tank": ["S_1002_1", "S_1007_1", "S_1010_1", "S_1011_1",
                     "S_1015_1", "S_1016_1"],
            "assist": ["S_1004_1", "S_1009_1", "S_1010_1", "S_1011_1",
                       "S_1015_1"],
        }
        pool = pools.get(arch, pools["attack"])
        skill0 = pool[fam % len(pool)]
        skill1 = pool[(fam * 7 + 3) % len(pool)]
        eff = "E_%03d" % (1 + fam % 19)
        if hero:
            sign, dmg = hero["sign"], hero["damage"]
            hp0, hp1, ap0, ap1, d0, d1, d20, d21, spd, rng = hero["pl"]
        else:
            var = 0.9 + ((fam % 17) / 16.0) * 0.25
            hp0, hp1 = hp0 * var, hp1 * var
            ap0, ap1 = ap0 * var, ap1 * var
    dmg = DAMAGE_TYPE_OVERRIDES.get(base, dmg)
    # Summoned units use exactly one simple skill.  Their extra skill slots
    # are cleared here and again in _apply_summon_rules().
    if base in SUMMON_FAMILIES:
        _summon_kit = SUMMON_SKILLS.get(base) or SUMMON_DEFAULT_SKILL
        if _summon_kit:
            skill0 = _summon_kit[0]
        skill1 = ""
        eff = ""
    # Per-family client range override (pl[9]); e.g. 鋼鐵俠提摩 600,
    # 鋼鐵蘑菇 6500.
    rng = RANGE_OVERRIDES.get(base, rng)
    # Summons normally have no auto-attack effect; a few (鋼鐵蘑菇) fire a
    # visible projectile, so re-apply the per-family effect after the clear.
    eff = EFFECT_OVERRIDES.get(base, eff)
    # 6★ and the final 7★ tier share a base cap of 70; the independent
    # 極限突破 gate raises the cap by +30 to 100.  Lower stars keep the old
    # 30 + (star-2)*10 curve.
    if kind == 1:
        lv_max = 70 if star >= 6 else 30 + max(0, star - 2) * 10
    else:
        lv_max = 10
    # Exp materials (A_2001_*) give more exp at higher tiers.  The user's
    # classified food families (A_2006 etc.) are the real EXP materials; the
    # client refuses to swallow anything with offerExp > 50000, so use the
    # maximum legal value for testing (the exact original values are lost).
    if base in EXP_MATERIAL_FAMILIES or base in EXP_CROP_FAMILIES:
        offer_exp = 50000
    elif aid.startswith("A_2001_"):
        offer_exp = 100 * star
    elif aid.startswith(("A_3", "A_4")):
        # 2026-10-25: wild-monster fodder gives 4x swallow EXP (100 → 400).
        # Client and server both read tl[6], so the swallow panel and the
        # actual gain stay in sync without a SWF patch.
        offer_exp = 400
    else:
        offer_exp = 100
    offer_gold = 200 if kind == 1 else 50 * star
    if base in SWALLOW_SPECIAL_FAMILIES:
        # Keep offerGold/offerExp <= 1.5 so the client lets the player pick
        # skill cookies and the intimacy potion as swallow materials.  A very
        # low offerGold also raises their getSwallowValue() sort key above the
        # advance materials, making them easy to find in the 材料/小怪 tabs,
        # while staying below the 50k-EXP scrolls so 全選 still prefers food.
        offer_gold = 1
    if kind == 1 and star == 6:
        # 6★3阶 -> 7★: one kind-4 A_6 material.
        mats = ["A_6"]
    elif kind == 1 and star >= 7:
        mats = []
    else:
        mats = ["A_2001_4"] if meta.get("next") else []
    if kind == 4:
        # Material avatars are food/star-up stock, not combat units.  Leave
        # their combat skill slots empty; the client's Avatar.initSkills()
        # should not build SkillSets for them (A_6xxx entries otherwise hit
        # an undefined SkillSetData when the barracks list is built).
        skill0 = ""
        skill1 = ""
        eff = ""
    if base == "A_2107":
        # 2026-10-25 user: the small skill cookie is a material, not a
        # battle unit — clear the inherited assist skills/effect so its
        # detail page no longer shows combat skills.  The swallow skill-up
        # effect (SKILL_UP_CHANCE) is unchanged.
        skill0 = ""
        skill1 = ""
        eff = ""
    # 2026-10-20: restore per-character 統御 values.  The original server
    # table is not present in the client, so use the star curve (4★=8,
    # 5★=10, 6★=12) instead of the old flat test value 4.  The account level
    # is raised to 50 (cap = 50 + 10 = 60) so the 5-hero test team fits.
    lead = int(meta.get("leadership", star * 2)) if kind == 1 else 4
    return {
        "name": meta.get("name", aid),
        "res": meta.get("res", aid),
        # Usage description for material cards (empty for units/heroes).
        "desc": _material_desc(base, star, aid),
        # Original action tactic: 0 勇猛 / 1 策略 / 2 狡诈 / 3 坚守.
        # Towers and crystals (A_5xxx) always hold position.
        "tactic": 3 if base.startswith("A_5") else TACTIC_BY_FAMILY.get(base, 0),
        "tl": [sign, action, dmg, lead, lv_max, 1, offer_exp, offer_gold,
               mats],
        # pl[12] = effect set, pl[13] = passive skill (skillB).  AvatarData
        # reads pl[13] into skillB; the detail panel shows a third skill
        # button when it is non-empty.
        "pl": [int(hp0 * scale), int(hp1 * scale), int(ap0 * scale),
               int(ap1 * scale), d0, d1, d20, d21, spd, rng,
               skill0, skill1, eff, ""],
        # AvatarData.skillExp: direct percentage added to the 技能點 UI and
        # the server's skill-up roll.
        "skillup": int(SKILL_UP_CHANCE.get(aid, 0)),
        # AvatarData.loveExp: 魔法藥水's affection points (4★/5★/6★).
        "love": int(LOVE_POTION_GAIN.get(aid, 0)),
    }


# ---------------------------------------------------------------------------
# Hero-skill design rules
# ---------------------------------------------------------------------------
# Duration argument position for actions that create a persistent buff/debuff.
# Actions not listed here are direct damage, healing, movement, summoning or
# instant displacement and are not counted as buff/debuff applications.
_SKILL_BUFF_DURATION_INDEX = {
    "stun": 3,
    "silence": 3,
    "weak": 4,
    "sunder": 4,
    "poison": 4,
    "attrup": 4,
    "burn": 2,
    "shield": 2,
    "strong": 2,
    "steel": 2,
    "evil": 1,
    "purify": 1,
    "taunt": 1,
    "bless": 1,
}
_SKILL_BANNED = {
    "novice": {"sunder", "burn", "evil", "steel"},
    "advanced": {"evil", "steel"},
}
_SKILL_BUFF_LIMIT = {"novice": 2, "advanced": 4}
_SKILL_MAX_ROUNDS = {"novice": 1, "advanced": 2}
_SKILL_DAMAGE_ACTIONS = {
    "damage", "combo", "suck", "stun", "silence", "weak", "sunder",
    "poison", "burn", "pull", "push",
}
_SKILL_DAMAGE_CAP = {
    "novice": {"single": 0.90, "group": 0.45},
    "advanced": {"single": 1.30, "group": 0.60},
}
_SKILL_MAX_LEVEL = 5   # slv_config[0]


def _skill_target_count(pl):
    """Approximate number of units a skill's aoe value can touch."""
    try:
        aoe = int(pl[4] or 0)
    except (TypeError, ValueError):
        aoe = 0
    if aoe == 0:
        return 1
    if aoe < 0:
        return abs(aoe) + 1
    if aoe >= 199:
        return 999
    return aoe + 1


def _skill_is_group(pl):
    try:
        return int(pl[4] or 0) != 0
    except (TypeError, ValueError):
        return False


def _skill_damage_total(actions):
    total = 0.0
    for act in actions:
        if not (isinstance(act, list) and act):
            continue
        typ = act[0]
        if typ == "combo":
            try:
                total += float(act[1] or 0) * int(act[3] or 1)
            except (TypeError, ValueError, IndexError):
                pass
        elif typ in _SKILL_DAMAGE_ACTIONS:
            try:
                total += float(act[1] or 0)
            except (TypeError, ValueError, IndexError):
                pass
    return total


def _cap_skill_damage(pl, actions, tier, skill=None):
    """Scale all damage coefficients so the skill total stays under the cap.

    The cap is per skill, not per hit: a 3-hit combo with 0.4 each counts as
    1.2 total damage.  The skill-level bonus (``skillUp``) is included at the
    maximum skill level, so leveling a skill cannot push it over the budget.
    """
    cap_map = _SKILL_DAMAGE_CAP.get(tier)
    if not cap_map:
        return
    cap = cap_map["group" if _skill_is_group(pl) else "single"]
    total = _skill_damage_total(actions)
    if total <= 0:
        return

    extra = 0.0
    skill_up = skill.get("skillUp") if isinstance(skill, dict) else None
    if isinstance(skill_up, list) and len(skill_up) >= 2:
        try:
            up_index = int(skill_up[0])
            up_add = float(skill_up[1] or 0)
        except (TypeError, ValueError):
            up_index = -1
            up_add = 0.0
        if 0 <= up_index < len(actions) and up_add > 0:
            up_act = actions[up_index]
            if isinstance(up_act, list) and up_act:
                typ = up_act[0]
                if typ == "combo":
                    try:
                        extra = (up_add * (_SKILL_MAX_LEVEL - 1)
                                 * int(up_act[3] or 1))
                    except (TypeError, ValueError, IndexError):
                        extra = 0.0
                elif typ in _SKILL_DAMAGE_ACTIONS:
                    extra = up_add * (_SKILL_MAX_LEVEL - 1)

    if total + extra <= cap:
        return
    factor = cap / (total + extra) if (total + extra) > 0 else 0.0
    for act in actions:
        if not (isinstance(act, list) and act):
            continue
        typ = act[0]
        if typ != "combo" and typ not in _SKILL_DAMAGE_ACTIONS:
            continue
        try:
            act[1] = max(0.0, round(float(act[1] or 0) * factor, 3))
        except (TypeError, ValueError, IndexError):
            pass
    if isinstance(skill_up, list) and len(skill_up) >= 2 and extra > 0:
        try:
            skill_up[1] = max(0.0, round(float(skill_up[1] or 0) * factor, 3))
        except (TypeError, ValueError):
            pass


def _skill_fx(actions, fallback="E_001"):
    for act in reversed(actions):
        if isinstance(act, list) and act:
            for value in reversed(act[1:]):
                if isinstance(value, str) and value.startswith("E_"):
                    return value
    return fallback




def _detail_pct(v):
    try:
        return ("%g" % round(float(v) * 100.0, 2)) + "%"
    except (TypeError, ValueError):
        return str(v)


def _detail_dtype(v):
    return {1: "\u7269\u7406", 2: "\u9b54\u6cd5", 3: "\u771f\u5be6"}.get(
        int(v or 0), "\u9b54\u6cd5")


def _detail_stat(stat, value):
    """Buff stat label + displayed value (crit/tough are 0.1% units)."""
    if stat == "crit":
        return "\u66b4\u64ca\u7387+%g%%" % (float(value) / 10.0)
    if stat == "tough":
        return "\u97cc\u6027+%g%%" % (float(value) / 40.0)
    labels = {"hp": "\u751f\u547d", "ap": "\u653b\u64ca",
              "hit": "\u547d\u4e2d", "flee": "\u9583\u907f",
              "de_ph": "\u7269\u9632", "de_ma": "\u6cd5\u9632"}
    return labels.get(stat, str(stat)) + "+%d" % int(value)


def _skill_detail_text(skill):
    """Human-readable numeric summary for the 詳情 page (one line)."""
    parts = []
    for act in skill.get("skill") or []:
        if not (isinstance(act, list) and act):
            continue
        t = act[0]
        try:
            if t == "damage":
                p = "\u50b7\u5bb3 %s\u653b\u64ca\uff08%s\uff09" % (
                    _detail_pct(act[1]), _detail_dtype(act[2]))
            elif t == "combo":
                p = "\u50b7\u5bb3 %s\u653b\u64ca\u00d7%d\uff08%s\uff09" % (
                    _detail_pct(act[1]), int(act[3]), _detail_dtype(act[2]))
            elif t == "suck":
                p = "\u50b7\u5bb3 %s\u653b\u64ca\uff08%s\uff09\uff0c\u5438\u8840 %s" % (
                    _detail_pct(act[1]), _detail_dtype(act[2]),
                    _detail_pct(act[3]))
            elif t in ("stun", "silence"):
                _cc_dmg = ""
                if act[1]:
                    _cc_dmg = "\uff1b\u50b7\u5bb3 %s\u653b\u64ca\uff08%s\uff09" % (
                        _detail_pct(act[1]), _detail_dtype(act[2]))
                p = "%s%d\u56de\u5408%s" % (
                    "\u7729\u6688" if t == "stun" else "\u6c89\u9ed8", int(act[3]), _cc_dmg)
            elif t == "evil":
                p = "\u8a5b\u5492%d\u56de\u5408" % int(act[1])
            elif t == "evilall":
                p = "\u6575\u65b9\u5168\u9ad4\u8a5b\u5492%d\u56de\u5408" % int(act[1])
            elif t == "miasmafield":
                p = "\u5c55\u958b\u7634\u6c23\u9818\u57df%d\u56de\u5408\uff1a\u6211\u65b9\u65bd\u6bd2\u758a\u5c64+100%%" % int(act[1])
            elif t in ("weak", "sunder"):
                _ws_dmg = ""
                if act[1]:
                    _ws_dmg = "\uff1b\u50b7\u5bb3 %s\u653b\u64ca\uff08%s\uff09" % (
                        _detail_pct(act[1]), _detail_dtype(act[2]))
                p = "%s%d\u56de\u5408%s" % (
                    "\u865b\u5f31" if t == "weak" else "\u7834\u7532", int(act[4]), _ws_dmg)
            elif t == "poison":
                # 2026-10-23: a pure poison application (coeff 0) should not
                # print a meaningless "damage 0%".
                _poison_dmg = ""
                if act[1]:
                    _poison_dmg = "\u50b7\u5bb3 %s\u653b\u64ca\uff1b" % _detail_pct(act[1])
                p = "%s\u4e2d\u6bd2\uff1a\u6bcf\u5c64 %s\u653b\u64ca + 2%%\u6700\u5927\u751f\u547d\uff0c\u6700\u591a10\u5c64\uff0c\u6301\u7e8c%d\u56de\u5408" % (
                    _poison_dmg, _detail_pct(float(act[3]) * 0.2), int(act[4]))
            elif t == "burn":
                p = "\u71c3\u71d2%d\u56de\u5408\uff08\u6bcf\u56de\u5408 %s\u653b\u64ca\uff09" % (
                    int(act[2]), _detail_pct(act[1]))
            elif t in ("pull", "push"):
                p = "\u50b7\u5bb3 %s\u653b\u64ca\uff1b%s%d" % (
                    _detail_pct(act[1]),
                    "\u62c9\u8fd1" if t == "pull" else "\u64ca\u9000",
                    int(act[3]))
            elif t == "shield":
                p = "\u8b77\u76fe %s\u653b\u64ca\uff0c%d\u56de\u5408" % (
                    _detail_pct(act[1]), int(act[2]))
            elif t == "strong":
                p = "\u653b\u64ca+%s\uff0c%d\u56de\u5408" % (
                    _detail_pct(act[1]), int(act[2]))
            elif t == "steel":
                p = "\u97cc\u6027+%s\uff0c%d\u56de\u5408" % (
                    _detail_pct(act[1]), int(act[2]))
            elif t == "cure":
                p = "\u6cbb\u7642 %s\u653b\u64ca" % _detail_pct(act[1])
            elif t == "hpcure":
                p = "\u6cbb\u7642 %d + %s\u6700\u5927\u751f\u547d" % (
                    int(act[1]), _detail_pct(act[2]))
            elif t == "purify":
                p = "\u6de8\u5316%d\u56de\u5408" % int(act[1])
            elif t == "bless":
                p = "\u795e\u4f51%d\u56de\u5408" % int(act[1])
            elif t == "taunt":
                p = "\u5632\u8b35%d\u56de\u5408" % int(act[1])
            elif t == "summon":
                p = "\u53ec\u559a%s\uff08%s\u5c6c\u6027\uff09\uff0c%d\u56de\u5408" % (
                    act[2], _detail_pct(act[1]), int(act[3]))
            elif t == "summon_ratio":
                p = "\u53ec\u559a%s\uff1a\u751f\u547d%s/\u653b\u64ca%s/\u5176\u4ed6%s\uff0c%d\u56de\u5408" % (
                    act[4], _detail_pct(act[1]), _detail_pct(act[2]),
                    _detail_pct(act[3]), int(act[5]))
            elif t == "dash":
                p = "\u4f4d\u79fb%d" % int(act[1])
            elif t == "reline":
                p = "\u50b3\u9001\u81f3\u6700\u8fd1\u6230\u7dda"
            elif t == "line_damage":
                hit = act[4] if len(act) > 4 else 0
                p = "\u5168\u7dda\uff1a%s\u653b\u64ca + %s\u547d\u4e2d" % (
                    _detail_pct(act[1]), _detail_pct(hit))
            elif t == "rotline":
                p = "全線：%s攻擊 + 目標每層中毒 %s最大生命（魔法）；施加%d層中毒，持續%d回合" % (
                    _detail_pct(act[1]), _detail_pct(act[2]), 1,
                    int(act[4]))
            elif t == "miasma":
                p = "全體：詛咒%d回合、中毒%d回合，然後 %d + %s攻擊（魔法）；瘴氣領域%d回合：我方中毒疊層+100%%" % (
                    int(act[3]), int(act[4]), int(act[1]),
                    _detail_pct(act[2]), int(act[5]))
            elif t == "toxburst":
                p = "敵人中毒≥7層時引爆：%d + %s攻擊 + 每層%s最大生命（魔法），並清空該目標中毒" % (
                    int(act[1]), _detail_pct(act[2]),
                    _detail_pct(act[3]))
            elif t == "poisonarrow":
                p = "鎖定中毒層數最高：%s攻擊（魔法）；施加1層中毒，持續%d回合" % (
                    _detail_pct(act[1]), int(act[3]))
            elif t == "poisonbolts":
                p = "%d發：每發 %s攻擊（%s）+ 1層中毒，持續%d回合" % (
                    int(act[1]), _detail_pct(act[2]), _detail_dtype(act[5]),
                    int(act[4]))
            elif t == "atkcure":
                p = "我方全體回復 %d + %s攻擊" % (
                    int(act[1]), _detail_pct(act[2]))
            elif t == "atkblast":
                p = "敵方全體：%d + %s攻擊（魔法）" % (
                    int(act[1]), _detail_pct(act[2]))
            elif t == "atkshield":
                p = "護盾 %d + %s攻擊，%d回合" % (
                    int(act[1]), _detail_pct(act[2]), int(act[3]))
            elif t == "neurotoxin":
                p = "形態1（0-4層）：最近敵人 %s攻擊（魔法），中毒%d回合；形態2（5-12層）：全線 %s攻擊（魔法）+詛咒1回合；形態3（≥13層）：全體 %s攻擊（魔法）+詛咒、虛弱1回合；均附加中毒%d回合" % (
                    _detail_pct(act[1]), int(act[5]), _detail_pct(act[2]),
                    _detail_pct(act[3]), int(act[5]))
            elif t == "webstun":
                if len(act) >= 8:
                    p = ("敵方全體：%s攻擊（魔法），並施加中毒%d回合；"
                         "中毒≥%d層額外眩暈%d回合") % (
                        _detail_pct(act[1]), int(act[6]), int(act[2]),
                        int(act[3]))
                else:
                    p = "敵方全體：%s攻擊（魔法）；中毒≥%d層額外眩暈%d回合" % (
                        _detail_pct(act[1]), int(act[2]), int(act[3]))
            elif t == "drain_barrage":
                p = "%d\u6bb5\u00d7%s\u653b\u64ca\uff0c\u5438\u8840%s" % (
                    int(act[1]), _detail_pct(act[2]), _detail_pct(act[3]))
            elif t == "darkwave":
                p = "\u5168\u9ad4\uff1a%d + %s\u653b\u64ca\uff0c\u6c89\u9ed8%d\u56de\u5408" % (
                    int(act[1]), _detail_pct(act[2]), int(act[4]))
            elif t == "darkbolt":
                p = "%s\u653b\u64ca\uff1b\u8a5b\u5492%d\u56de\u5408\uff0c\u4e2d\u6bd2%s/\u56de\u5408\uff0c\u865b\u5f31%s" % (
                    _detail_pct(act[1]), int(act[3]), _detail_pct(act[4]),
                    _detail_pct(act[5]))
            elif t == "hpshield_flat":
                p = "\u8b77\u76fe %d + %s\u6700\u5927\u751f\u547d\uff0c%d\u56de\u5408" % (
                    int(act[1]), _detail_pct(act[2]), int(act[3]))
            elif t == "damage_shield":
                p = "\u8b77\u76fe %d + \u672c\u6b21\u50b7\u5bb3%s\uff0c%d\u56de\u5408" % (
                    int(act[1]), _detail_pct(act[2]), int(act[3]))
            elif t == "damage_cure":
                p = "\u56de\u5fa9\u672c\u6b21\u50b7\u5bb3%s" % _detail_pct(act[1])
            elif t in ("flatbuff", "flatbuff_self"):
                p = "%s\uff0c%d\u56de\u5408" % (
                    _detail_stat(act[1], act[2]), int(act[3]))
            elif t == "spores":
                p = "%d\u6b21\u55ae\u9ad4\uff1a%s\u653b\u64ca + %s\u547d\u4e2d" % (
                    int(act[1]), _detail_pct(act[3]), _detail_pct(act[4]))
            elif t == "froststorm":
                p = "\u5168\u9ad4\uff1a%d + %s\u653b\u64ca + %s\u751f\u547d + %s\u97cc\u6027\uff1b\u56de\u5fa9%s\u50b7\u5bb3" % (
                    int(act[1]), _detail_pct(act[2]), _detail_pct(act[3]),
                    _detail_pct(act[4]), _detail_pct(act[5]))
            elif t == "frostlance":
                p = "%d + %s\u653b\u64ca + %s\u751f\u547d\uff1b\u7834\u7532%s/\u865b\u5f31%s\uff0c%d\u56de\u5408" % (
                    int(act[1]), _detail_pct(act[2]), _detail_pct(act[3]),
                    _detail_pct(act[4]), _detail_pct(act[5]), int(act[6]))
            elif t == "inferno":
                p = "\u5168\u9ad4\uff1a%d + %s\u751f\u547d + %s\u653b\u64ca + %s\u547d\u4e2d\uff1b\u71c3\u71d2%d\u56de\u5408\uff08%s\u653b\u64ca\uff09\uff0c\u8a5b\u5492%d\u56de\u5408" % (
                    int(act[1]), _detail_pct(act[2]), _detail_pct(act[3]),
                    _detail_pct(act[4]), int(act[6]), _detail_pct(act[5]),
                    int(act[7]))
            elif t == "hellstar":
                p = "\u55ae\u9ad4\uff1a%d + %s\u653b\u64ca + %s\u547d\u4e2d" % (
                    int(act[1]), _detail_pct(act[2]), _detail_pct(act[3]))
            elif t == "devilpact":
                p = "\u6d88\u8017\u7576\u524d\u751f\u547d30%%\uff1b%d\u6bb5\uff1a%d + \u640d\u5931\u751f\u547d%s\uff0c\u8a5b\u5492%d\u56de\u5408" % (
                    int(act[3]), int(act[1]), _detail_pct(act[2]), int(act[4]))
            elif t == "hpdmg":
                p = "%s\u6700\u5927\u751f\u547d + %s\u653b\u64ca\uff08%s\uff09" % (
                    _detail_pct(act[1]), _detail_pct(act[2]), _detail_dtype(act[3]))
            elif t == "hpshield":
                p = "\u8b77\u76fe %s\u6700\u5927\u751f\u547d\uff0c%d\u56de\u5408" % (
                    _detail_pct(act[1]), int(act[2]))
            elif t == "puredebuff":
                p = "\u65bd\u52a0%s\uff0c%d\u56de\u5408" % (act[1], int(act[3]))
            elif t == "healup":
                p = "\u6cbb\u7642\u6548\u679c+%s" % _detail_pct(act[1])
            elif t == "attrup":
                p = "\u63d0\u5347\u5c6c\u6027\uff0c%d\u56de\u5408" % int(act[4])
            elif t in ("delay", "passive"):
                continue
            else:
                continue
        except (IndexError, TypeError, ValueError):
            continue
        parts.append(p)
    return "\uff1b".join(parts)


def _skill_dtype(actions, default=1):
    for act in actions:
        if not (isinstance(act, list) and len(act) > 2):
            continue
        if act[0] in ("damage", "combo", "suck", "stun", "silence",
                      "weak", "sunder", "poison", "pull", "push"):
            try:
                return int(act[2])
            except (TypeError, ValueError):
                pass
    return default


def _enrich_skill(pl, actions, tier, arch):
    """Give a bare damage/heal skill one simple secondary effect.

    Only skills whose target count already fits the tier's buff-unit limit
    are enriched, so adding the effect does not force the aoe down later.
    """
    if tier not in _SKILL_BUFF_LIMIT:
        return
    max_actions = 3 if tier == "novice" else 4
    if len(actions) >= max_actions:
        return
    if any(isinstance(a, list) and a and a[0] in _SKILL_BUFF_DURATION_INDEX
           for a in actions):
        return
    target_count = _skill_target_count(pl)
    unit_limit = _SKILL_BUFF_LIMIT[tier]
    if target_count > unit_limit:
        return
    has_damage = any(
        isinstance(a, list) and a and a[0] in _SKILL_DAMAGE_ACTIONS
        for a in actions)
    fx = _skill_fx(actions)
    duration = 1 if tier == "novice" else 2
    if not has_damage:
        # Pure heal/support: add a small ally buff.
        if arch == "tank":
            actions.append(["shield", 0.4 if tier == "novice" else 0.5,
                            duration, fx])
        else:
            actions.append(["strong", 0.2 if tier == "novice" else 0.3,
                            duration, fx])
        return
    dtype = _skill_dtype(actions)
    if arch == "tank":
        actions.append(["stun", 0, dtype, duration, fx])
    elif arch == "attack":
        if tier == "advanced":
            actions.append(["sunder", 0, dtype, 0.3, duration, fx])
        else:
            actions.append(["weak", 0, dtype, 0.2, duration, fx])
    elif arch == "mage":
        if tier == "advanced":
            actions.append(["burn", 0.2, duration, fx])
        else:
            actions.append(["silence", 0, dtype, duration, fx])
    else:  # assist
        if tier == "advanced":
            actions.append(["silence", 0, dtype, duration, fx])
        else:
            actions.append(["weak", 0, dtype, 0.2, duration, fx])


def _pct(value):
    try:
        return int(round(float(value or 0) * 100))
    except (TypeError, ValueError):
        return 0


def _dtype_name(value):
    try:
        return {1: "物理", 2: "魔法", 3: "真實"}.get(int(value), "物理")
    except (TypeError, ValueError):
        return "物理"


def _target_text(pl, support=False):
    try:
        aoe = int(pl[4] or 0)
        rng = int(pl[2] or 0)
    except (TypeError, ValueError, IndexError):
        aoe = 0
        rng = 0
    if support:
        if aoe == 0:
            return "自身" if rng == 0 else "友方單體"
        if aoe >= 199:
            return "友方全體"
        if aoe < 0:
            return "隨機%d個友方" % (abs(aoe) + 1)
        return "最多%d個友方" % min(aoe + 1, 6)
    if aoe == 0:
        return "敵方單體"
    if aoe == 199 or aoe >= 200:
        return "直線/範圍內敵人"
    if aoe < 0:
        return "隨機%d個敵人" % (abs(aoe) + 1)
    return "最多%d個敵人" % min(aoe + 1, 6)


def _build_skill_info(pl, actions):
    """Generate a description that always matches the final action list.

    Damage-bearing actions are merged by damage type so a skill reads as one
    coherent hit instead of repeating "對...造成..." for every action.
    """
    enemy = _target_text(pl, False)
    ally = _target_text(pl, True)
    prefixes = []
    damage_by_dtype = {}
    damage_segments = 0
    effects = []
    heal_ratio = 0.0
    support = []
    for act in actions:
        if not (isinstance(act, list) and act):
            continue
        typ = act[0]
        try:
            if typ == "dash":
                prefixes.append("向前突進")
            elif typ == "reline":
                prefixes.append("轉移至最近戰線")
            elif typ == "gank":
                prefixes.append("召集同線友軍集火")
            elif typ in ("damage", "combo", "suck", "stun", "silence",
                         "weak", "sunder", "poison", "pull", "push"):
                coeff = float(act[1] or 0)
                dtype = int(act[2]) if len(act) > 2 else 1
                if typ == "combo":
                    times = int(act[3] or 1)
                    coeff *= times
                    if coeff > 0:
                        damage_segments += times
                elif typ in ("damage", "suck") and coeff > 0:
                    damage_segments += 1
                if coeff > 0:
                    damage_by_dtype[dtype] = (
                        damage_by_dtype.get(dtype, 0.0) + coeff)
                if typ == "suck":
                    heal_ratio = float(act[3] or 0) if len(act) > 3 else 0
                elif typ in ("stun", "silence"):
                    effects.append(
                        ("眩暈" if typ == "stun" else "沉默")
                        + "%d回合" % int(act[3] or 0))
                elif typ in ("weak", "sunder"):
                    effects.append(
                        ("虛弱" if typ == "weak" else "破防")
                        + "%d回合" % int(act[4] or 0))
                elif typ == "poison":
                    effects.append("中毒%d回合" % int(act[4] or 0))
                elif typ == "pull":
                    effects.append("被拉拽")
                elif typ == "push":
                    effects.append("被擊退")
            elif typ == "burn":
                support.append("使%s引燃%d回合" % (
                    enemy, int(act[2] or 0)))
            elif typ == "evil":
                support.append("對%s施加詛咒%d回合" % (
                    enemy, int(act[1] or 0)))
            elif typ == "shield":
                support.append("為%s附加攻擊%d%%的護盾%d回合" % (
                    ally, _pct(act[1]), int(act[2] or 0)))
            elif typ == "cure":
                support.append("為%s回復攻擊%d%%的生命" % (
                    ally, _pct(act[1])))
            elif typ == "strong":
                support.append("為%s提升%d%%攻擊%d回合" % (
                    ally, _pct(act[1]), int(act[2] or 0)))
            elif typ == "steel":
                support.append("為%s提升%d%%防禦%d回合" % (
                    ally, _pct(act[1]), int(act[2] or 0)))
            elif typ == "purify":
                support.append("為%s淨化%d回合" % (
                    ally, int(act[1] or 0)))
            elif typ == "attrup":
                attr = {"hit": "命中", "flee": "閃避",
                        "crit": "暴擊", "tough": "韌性"}.get(
                            act[2] if len(act) > 2 else "", "屬性")
                support.append("為%s提升%d%%%s%d回合" % (
                    ally, _pct(act[1]), attr, int(act[4] or 0)))
            elif typ == "taunt":
                support.append("嘲諷敵人%d回合" % int(act[1] or 0))
            elif typ == "bless":
                support.append("為%s附加神佑%d回合" % (
                    ally, int(act[1] or 0)))
            elif typ == "summon":
                support.append("召喚%s（等級%d%%）%d回合" % (
                    act[2] if len(act) > 2 else "召喚物",
                    _pct(act[1]), int(act[3] or 0)))
        except (TypeError, ValueError, IndexError):
            pass
    phrases = list(prefixes)
    if damage_by_dtype:
        parts = []
        for dtype, total in damage_by_dtype.items():
            parts.append("%d%%%s" % (_pct(total), _dtype_name(dtype)))
        text = "對%s造成%s傷害" % (enemy, "與".join(parts))
        if damage_segments > 1:
            text += "（%d段）" % damage_segments
        if heal_ratio > 0:
            text += "並回復傷害%d%%的生命" % _pct(heal_ratio)
        if effects:
            text += "並" + "、".join(effects)
        phrases.append(text)
    elif effects:
        phrases.append("使%s%s" % (enemy, "、".join(effects)))
    phrases.extend(support)
    if not phrases:
        return "無額外效果。"
    return "，".join(phrases) + "。"


def _constrain_skill(skill, tier, kind, arch="attack"):
    """Apply the novice/advanced skill restrictions to one skill dict.

    ``kind`` is "normal" (英雄技) or "leader" (队长技).  The client has a
    single skill-level ``aoe`` value shared by all actions, so a skill that
    mixes damage with buff/debuff has to obey the stricter buff-unit limit.
    """
    if not isinstance(skill, dict):
        return
    if tier not in ("novice", "advanced"):
        return
    pl = skill.get("pl")
    if isinstance(pl, list) and len(pl) >= 2:
        try:
            pl[1] = max(1, int(pl[1] or 0))
        except (TypeError, ValueError):
            pl[1] = 1
    actions = skill.get("skill")
    if not isinstance(actions, list):
        return
    banned = _SKILL_BANNED.get(tier, set())
    limit = _SKILL_BUFF_LIMIT.get(tier, 999)
    max_rounds = _SKILL_MAX_ROUNDS.get(tier, 999)
    kept = []
    buff_count = 0
    for act in actions:
        if not (isinstance(act, list) and act):
            kept.append(act)
            continue
        typ = act[0]
        if typ in banned:
            continue
        duration_index = _SKILL_BUFF_DURATION_INDEX.get(typ)
        if duration_index is not None:
            if buff_count >= limit:
                continue
            if len(act) > duration_index:
                try:
                    act[duration_index] = min(int(act[duration_index]),
                                              max_rounds)
                except (TypeError, ValueError):
                    pass
            buff_count += 1
        kept.append(act)
    skill["skill"] = kept

    if not (isinstance(pl, list) and len(pl) >= 5):
        return
    has_buff = any(
        isinstance(act, list) and act and act[0] in _SKILL_BUFF_DURATION_INDEX
        for act in kept)
    has_damage = any(
        isinstance(act, list) and act and act[0] in _SKILL_DAMAGE_ACTIONS
        for act in kept)

    # Novice skill range is capped at 600; keep the sign so ally-target
    # skills (negative range) still work.
    if tier == "novice":
        try:
            raw_range = int(pl[2] or 0)
        except (TypeError, ValueError):
            raw_range = 0
        sign = -1 if raw_range < 0 else 1
        pl[2] = sign * min(abs(raw_range), 600)

    try:
        aoe = int(pl[4] or 0)
    except (TypeError, ValueError):
        aoe = 0

    if kind == "normal":
        if tier == "novice":
            # Max 3 targets; a skill with buff/debuff may only touch 2 units.
            target_limit = 1 if has_buff else 2
            if aoe == 199 or aoe >= 200 or aoe > target_limit:
                aoe = target_limit
            elif aoe < -target_limit:
                aoe = -target_limit
        elif tier == "advanced":
            # Normal group damage max 5 targets; a line-wide skill (199) is
            # allowed.  Buff/debuff is limited to 4 units.
            target_limit = 3 if has_buff else 4
            if has_buff:
                if aoe >= 199 or aoe > target_limit:
                    aoe = target_limit
                elif aoe < -target_limit:
                    aoe = -target_limit
            elif has_damage:
                if aoe >= 200:
                    aoe = 199
                elif aoe > target_limit:
                    aoe = target_limit
                elif aoe < -target_limit:
                    aoe = -target_limit
    else:  # leader
        if tier == "novice":
            # Damage may hit one line (199) but never the whole enemy team.
            # Buff/debuff may only touch 2 units.
            if has_buff:
                target_limit = 1
                if aoe >= 199 or aoe > target_limit:
                    aoe = target_limit
                elif aoe < -target_limit:
                    aoe = -target_limit
            elif has_damage:
                # Keep the 199 line-wide sentinel, but a non-line area may
                # not cover the whole five-hero enemy team.
                if aoe == 199:
                    pass
                elif aoe >= 200:
                    aoe = 199
                elif aoe > 3:
                    aoe = 3
                elif aoe < -3:
                    aoe = -3
        elif tier == "advanced":
            # Leader damage is unlimited; buff/debuff is limited to 4 units.
            if has_buff:
                target_limit = 3
                if aoe >= 199 or aoe > target_limit:
                    aoe = target_limit
                elif aoe < -target_limit:
                    aoe = -target_limit

    pl[4] = aoe

    # First fill a bare skill with one simple tier-appropriate effect, then
    # enforce the tier damage budget and regenerate the description.
    _enrich_skill(pl, kept, tier, arch)
    if tier == "novice" and len(kept) > 3:
        # Novice skills should stay simple: dash + damage + one effect is
        # already enough.  Keep the primary actions authored first.
        kept = kept[:3]
    skill["skill"] = kept
    _cap_skill_damage(pl, kept, tier, skill)
    skill["info"] = _build_skill_info(pl, kept)


def _apply_skill_tier_rules(merged, skills):
    """Enforce novice/advanced restrictions on hero normal/leader skills.

    The rule is applied per skill id using the strictest tier that uses it, so
    a shared generic kit cannot bypass the novice limits.  High-tier heroes
    are intentionally left unrestricted.
    """
    tier_map = _gallery_tier_map()
    all_users = {}
    for aid, entry in merged.items():
        base = aid.rsplit("_", 1)[0]
        tier = tier_map.get(base)
        if tier not in ("novice", "advanced", "high"):
            continue
        pl = entry.get("pl")
        if not (isinstance(pl, list) and len(pl) >= 12):
            continue
        meta = AVATAR_CATALOG.get(aid) or {}
        arch = ARCH_OVERRIDES.get(base, meta.get("arch", "attack"))
        for slot, sid, kind in ((10, pl[10], "normal"),
                                (11, pl[11], "leader")):
            if sid in skills:
                all_users.setdefault(sid, []).append(
                    (aid, tier, kind, slot, arch))

    for sid, users in all_users.items():
        tiers = {user[1] for user in users}
        if not (tiers & {"novice", "advanced"}):
            continue
        if len(tiers) == 1:
            tier = next(iter(tiers))
            kinds = {user[2] for user in users}
            # A skill shared by a normal and a leader slot must satisfy the
            # stricter normal-skill target rules.
            kind = "normal" if "normal" in kinds else "leader"
            arch = users[0][4]
            skill = copy.deepcopy(skills[sid])
            _constrain_skill(skill, tier, kind, arch)
            skills[sid] = skill
        else:
            # The same kit is used by heroes of different tiers (for example
            # a base novice hero and its high-tier skin).  Clone it per tier
            # so the high-tier card keeps its unrestricted version.
            clones = {}
            for aid, tier, kind, slot, arch in users:
                key = (tier, kind)
                new_sid = clones.get(key)
                if new_sid is None:
                    new_sid = "%s_%s%s" % (sid, tier[0], kind[0])
                    clone = copy.deepcopy(skills[sid])
                    _constrain_skill(clone, tier, kind, arch)
                    skills[new_sid] = clone
                    clones[key] = new_sid
                entry = merged.get(aid)
                pl = entry.get("pl") if entry else None
                if isinstance(pl, list) and len(pl) > slot:
                    pl[slot] = new_sid

    # Hero skill + leader skill warmup must total at least one round.
    hero_pairs = []
    tier_map = _gallery_tier_map()
    for aid, entry in merged.items():
        base = aid.rsplit("_", 1)[0]
        if tier_map.get(base) not in ("novice", "advanced"):
            continue
        pl = entry.get("pl")
        if not (isinstance(pl, list) and len(pl) >= 12):
            continue
        normal_id, leader_id = pl[10], pl[11]
        if normal_id in skills and leader_id in skills:
            hero_pairs.append((normal_id, leader_id))

    need_normal = {}
    for normal_id, leader_id in hero_pairs:
        normal_skill = skills.get(normal_id) or {}
        leader_skill = skills.get(leader_id) or {}
        normal_pl = normal_skill.get("pl")
        leader_pl = leader_skill.get("pl")
        if not (isinstance(normal_pl, list) and len(normal_pl) >= 1):
            continue
        if not (isinstance(leader_pl, list) and len(leader_pl) >= 1):
            continue
        try:
            warmup_normal = int(normal_pl[0] or 0)
            warmup_leader = int(leader_pl[0] or 0)
        except (TypeError, ValueError):
            continue
        if warmup_normal + warmup_leader < 1:
            need_normal[normal_id] = max(
                need_normal.get(normal_id, 0), 1 - warmup_leader)
    for sid, need in need_normal.items():
        skill = skills.get(sid)
        if not isinstance(skill, dict):
            continue
        pl = skill.get("pl")
        if isinstance(pl, list) and len(pl) >= 1:
            try:
                pl[0] = max(int(pl[0] or 0), need)
            except (TypeError, ValueError):
                pl[0] = need

    # Apply the renamed buff vocabulary to every skill description, including
    # high-tier skills whose info text was not regenerated above.
    for skill in skills.values():
        if not isinstance(skill, dict):
            continue
        info = skill.get("info")
        if not isinstance(info, str):
            continue
        info = (info.replace("灼燒", "引燃")
                    .replace("邪惡", "詛咒")
                    .replace("鋼鐵", "鐵壁")
                    .replace("強化自身", "提升自身攻擊"))
        skill["info"] = info


_SUMMON_ALLOWED_ACTIONS = {
    "damage", "stun", "poison", "cure", "reline", "spores",
    "damage_cure", "poisonbolts",
}


def _constrain_summon_skill(skill, tier=None):
    """Apply the summon design rules to one summoned-unit skill.

    Only damage / stun / poison / ally-heal actions survive.  Stun and
    poison last at most 2 rounds on a single target and 1 round when the
    skill hits a group; a novice owner is stricter (1 round everywhere).
    Damage is capped at the owner tier's budget.
    """
    if not isinstance(skill, dict):
        return
    pl = skill.get("pl")
    if not (isinstance(pl, list) and len(pl) >= 5):
        pl = [0, 2, 300, 0, 0, 1]
        skill["pl"] = pl
    group = _skill_is_group(pl)
    kept = []
    for act in skill.get("skill") or []:
        if not (isinstance(act, list) and act):
            continue
        typ = act[0]
        if typ not in _SUMMON_ALLOWED_ACTIONS:
            continue
        if typ in ("stun", "poison"):
            idx = 3 if typ == "stun" else 4
            if len(act) > idx:
                try:
                    duration = int(act[idx] or 1)
                except (TypeError, ValueError):
                    duration = 1
                cap = 1 if group else 2
                if tier == "novice":
                    cap = min(cap, 1)
                act[idx] = max(1, min(duration, cap))
        kept.append(act)
    if not kept:
        dtype = _skill_dtype([], 2)
        kept = [["damage", 0.5, dtype, "E_009"]]
    skill["skill"] = kept
    skill["skillUp"] = [0, 0]
    if tier in ("novice", "advanced"):
        _cap_skill_damage(pl, kept, tier, skill)


def _apply_summon_rules(merged, skills):
    """Enforce the 2026-10-20 summon rules.

    * one skill per summon unit (skill0; skill1 and skillB cleared)
    * summon duration <= 2 rounds
    * owner scaling ratio clamped to 0.50..0.80
    * novice/advanced owners: damage/stun/poison/heal only, with the
      single-target / group duration caps and the owner's damage budget
    """
    owner_tiers = {}
    tier_map = _gallery_tier_map()
    for aid, entry in merged.items():
        base = aid.rsplit("_", 1)[0]
        tier = tier_map.get(base)
        if tier not in ("novice", "advanced", "high"):
            continue
        pl = entry.get("pl")
        if not (isinstance(pl, list) and len(pl) >= 12):
            continue
        for sid in (pl[10], pl[11]):
            skill = skills.get(sid)
            if not isinstance(skill, dict):
                continue
            for act in skill.get("skill") or []:
                if isinstance(act, list) and act and act[0] == "summon":
                    sbase = str(act[2]).rsplit("_", 1)[0]
                    owner_tiers.setdefault(sbase, set()).add(tier)

    # Owner-relative stats/levels: 50%-80% of the owner.  Summons never last
    # more than two rounds.
    for skill in skills.values():
        if not isinstance(skill, dict):
            continue
        for act in skill.get("skill") or []:
            if not (isinstance(act, list) and act and act[0] == "summon"):
                continue
            try:
                ratio = float(act[1])
            except (TypeError, ValueError, IndexError):
                ratio = 0.6
            act[1] = round(min(0.8, max(0.5, ratio)), 2)
            try:
                duration = int(act[3])
            except (TypeError, ValueError, IndexError):
                duration = 2
            act[3] = min(2, max(1, duration))

    # Exactly one skill per summon unit.  Shared summon families follow the
    # strictest owner tier.
    for aid, entry in merged.items():
        base = aid.rsplit("_", 1)[0]
        if base not in SUMMON_FAMILIES:
            continue
        pl = entry.get("pl")
        if not (isinstance(pl, list) and len(pl) >= 14):
            continue
        tiers = owner_tiers.get(base) or set()
        if "novice" in tiers:
            tier = "novice"
        elif "advanced" in tiers:
            tier = "advanced"
        else:
            tier = None
        skill = skills.get(pl[10])
        if isinstance(skill, dict):
            _constrain_summon_skill(skill, tier)
        pl[11] = ""
        pl[13] = ""


def _merge_avatars(overrides, skills):
    """Catalog entries first; hand-written heroes override individual fields.

    A whole-entry ``dict.update`` would drop ``name``/``res`` from the
    generated catalog entry (the overrides only carry tl/pl), leaving blank
    names in barracks/shop lists.  Merge per field instead.
    """
    merged = {aid: _avatar_entry(aid, meta)
              for aid, meta in AVATAR_CATALOG.items()}
    for aid, ov in overrides.items():
        base = merged.get(aid)
        if isinstance(base, dict):
            entry = dict(base)
            # The hand-written A_10xx entries are legacy fight-test data.
            # Gallery heroes now use the three-tier template, so keep the
            # generated pl/tl and only merge presentation fields such as
            # ``res`` (the sign-in plant overrides need their res mapping).
            if aid.rsplit("_", 1)[0] in HERO_INDEX:
                ov = {k: v for k, v in ov.items() if k not in ("pl", "tl")}
            entry.update(ov)
            merged[aid] = entry
        else:
            entry = dict(ov)
            entry.setdefault("name", aid)
            entry.setdefault("res", aid)
            merged[aid] = entry
    # 進階 (star-up) reads tl[8] as the list of acceptable material avatar
    # ids.  An empty list leaves every slot invalid and the 升星 button only
    # pops "請放入升星材料".  Use a kind-4 (材料) avatar one star below the
    # target; PVE also drops those so upgrades are sustainable.
    material_pool = {}
    for mid, meta in AVATAR_CATALOG.items():
        if int(meta.get("kind", 1)) == 4:
            material_pool.setdefault(int(meta.get("star", 1)), []).append(mid)
    fallback = sorted(material_pool.get(1) or ["A_6003_1"])[0]
    for aid, entry in merged.items():
        tl = entry.get("tl")
        if isinstance(tl, list):
            while len(tl) < 9:
                tl.append([] if len(tl) == 8 else 0)
            meta = AVATAR_CATALOG.get(aid) or {}
            if int(meta.get("kind", 1)) == 1:
                # One specific material per star, exactly one copy.
                # The client matches the required id by substring against
                # owned avatar ids, so a concrete id pins the icon and the
                # server accepts only that family/star.
                try:
                    _star = int(aid.split("_")[2])
                except (IndexError, ValueError):
                    _star = 1
                _mat = STARUP_MATERIALS.get(_star)
                tl[8] = [_mat] if _mat else []
            elif not tl[8]:
                try:
                    star = int(aid.split("_")[2])
                except (IndexError, ValueError):
                    star = 2
                pool = material_pool.get(max(1, star - 1)) or []
                tl[8] = sorted(pool) if pool else [fallback]
    # Placeholder entry so ItemStarUpElement can render an empty required
    # slot whose id is the "A_6" prefix (it builds Avatar("A_6")).
    merged.setdefault("A_6", {
        "name": "升星材料", "res": "A_6003_1",
        "tl": [1, 1, 1, 4, 10, 1, 100, 50, []],
        "pl": [100, 1, 10, 1, 0, 0, 0, 0, 300, 250,
               "S_1000_1", "S_1001_1", "E_001"],
    })
    # Gallery table (PanelHelpAvatar sorts by tl[9]): show exactly one tile
    # per avatar family.  The panel has separate tabs for A_1 heroes,
    # A_2/A_3/A_4 monsters, A_5 buildings and A_6 materials; every family
    # needs a non-negative sortIndex or its tab stays empty.  The label is
    # the id itself until the name pass below overwrites it.
    displays = {}
    for aid in merged:
        if aid == "A_6" or not aid.startswith(
                ("A_1", "A_2", "A_3", "A_4", "A_5", "A_6")):
            continue
        try:
            base, star_s = aid.rsplit("_", 1)
            star = int(star_s)
            int(base.split("_")[1])
        except (ValueError, IndexError):
            continue
        meta = AVATAR_CATALOG.get(aid) or {}
        score = (1 if meta.get("res") == aid else 0, star)
        if base not in displays or score > displays[base][0]:
            displays[base] = (score, aid)
    for entry in merged.values():
        tl = entry.get("tl")
        if isinstance(tl, list):
            while len(tl) < 11:
                tl.append(0)
            tl[9] = -1
    for base, (_score, aid) in displays.items():
        try:
            fam = int(base.split("_")[1])
        except ValueError:
            continue
        entry = merged[aid]
        if base in GALLERY_HIDDEN:
            entry["tl"][9] = -1
        else:
            entry["tl"][9] = GALLERY_SORT_OVERRIDES.get(base, fam - 1000)
    # ---- 2026-10-21 leadership (统御) --------------------------------
    # Order the hero families exactly like PanelHelpAvatar does (sortIndex),
    # then apply the user's novice/advanced/high table and per-阶 growth.
    _hero_gallery = []
    for _base, (_score, _aid) in displays.items():
        if not _base.startswith("A_1"):
            continue
        _e = merged.get(_aid) or {}
        _pos = (_e.get("tl") or [0] * 10)[9]
        try:
            _pos = int(_pos)
        except (TypeError, ValueError):
            continue
        if _pos >= 0:
            _hero_gallery.append((_pos, _base))
    _hero_gallery.sort()
    for _idx, (_pos, _base) in enumerate(_hero_gallery, 1):
        _table = LEADERSHIP_TABLE[_lead_tier(_idx)]
        for _aid, _e in merged.items():
            if _aid.rsplit("_", 1)[0] != _base:
                continue
            if int((AVATAR_CATALOG.get(_aid) or {}).get("kind", 1)) != 1:
                continue
            try:
                _star = int(_aid.split("_")[2])
            except (IndexError, ValueError):
                continue
            _e["tl"][3] = _table.get(_star, _table.get(5, 0))
            _e["lead_phase"] = 1 if _star <= 5 else (2 if _star == 6 else 0)
    # ---- one-skill kits for summoned units -----------------------------
    # _avatar_entry points every SUMMON_FAMILIES entry at one of these ids.
    _summon_kits = list(SUMMON_SKILLS.values())
    if SUMMON_DEFAULT_SKILL:
        _summon_kits.append(SUMMON_DEFAULT_SKILL)
    for _sid, _kit in _summon_kits:
        skills[_sid] = copy.deepcopy(_kit)
    # ---- authentic hero names and skill kits ---------------------------
    # Each kit becomes cfg.skill entries; pl[10]/pl[11] are the
    # normal/leader skills read by AvatarData and the skill popup.
    # Some cards have different 5-star and 6-star leader skills
    # (e.g. 李靖 神龍擺尾 vs 真·神龍擺尾), so allow leader5/leader6.
    kit_ids = {}
    for i, (base, kit) in enumerate(HERO_SKILLS.items()):
        nid = "S_%d_1" % (9001 + i * 4)
        lid = "S_%d_1" % (9002 + i * 4)
        skills[nid] = kit["normal"]
        skills[lid] = kit["leader"]
        lid5 = lid6 = None
        if kit.get("leader5"):
            lid5 = "S_%d_1" % (9003 + i * 4)
            skills[lid5] = kit["leader5"]
        if kit.get("leader6"):
            lid6 = "S_%d_1" % (9004 + i * 4)
            skills[lid6] = kit["leader6"]
        kit_ids[base] = (nid, lid, lid5, lid6)
        for aid, entry in merged.items():
            if aid.rsplit("_", 1)[0] != base:
                continue
            pl = entry.get("pl")
            if not (isinstance(pl, list) and len(pl) >= 12):
                continue
            try:
                star = int(aid.rsplit("_", 1)[1])
            except (IndexError, ValueError):
                star = 1
            pl[10] = nid
            if star >= 6 and kit.get("leader6"):
                pl[11] = lid6
            elif star == 5 and kit.get("leader5"):
                pl[11] = lid5
            else:
                pl[11] = lid
    # ---- fallback kits for not-yet-identified hero families ------------
    # The catalog used to hand out skills from a tiny shared pool, which put
    # e.g. 真男人 on mages.  Until a family is added to HERO_SKILLS, give it
    # a neutral role-appropriate kit instead of a mismatched champion skill.
    generic_ids = {}
    for j, (arch, kit) in enumerate(GENERIC_SKILLS.items()):
        # Keep this range clear of the 4-per-kit HERO_SKILLS ids (9001+),
        # which reached S_92xx after the 2014 hero pass.
        nid = "S_%d_1" % (9601 + j * 2)
        lid = "S_%d_1" % (9602 + j * 2)
        skills[nid] = kit["normal"]
        skills[lid] = kit["leader"]
        generic_ids[arch] = (nid, lid)
    if generic_ids:
        for aid, entry in merged.items():
            base = aid.rsplit("_", 1)[0]
            if not base.startswith("A_1") or base in HERO_SKILLS:
                continue
            meta = AVATAR_CATALOG.get(aid) or {}
            if int(meta.get("kind", 1)) != 1:
                continue
            ids = generic_ids.get(meta.get("arch")) or generic_ids["attack"]
            pl = entry.get("pl")
            if isinstance(pl, list) and len(pl) >= 12:
                pl[10], pl[11] = ids
    # Skin/morph cards reuse the base champion's kit (including the
    # 5★/6★ leader variants) instead of the neutral role kit.
    for aid, entry in merged.items():
        base = aid.rsplit("_", 1)[0]
        src = SKIN_BASE.get(base)
        if not src or src not in kit_ids:
            continue
        nid, lid, lid5, lid6 = kit_ids[src]
        pl = entry.get("pl")
        if not (isinstance(pl, list) and len(pl) >= 12):
            continue
        try:
            star = int(aid.rsplit("_", 1)[1])
        except (IndexError, ValueError):
            star = 1
        pl[10] = nid
        if star >= 6 and lid6:
            pl[11] = lid6
        elif star == 5 and lid5:
            pl[11] = lid5
        else:
            pl[11] = lid
    # Passive skills (pl[13] -> AvatarData.skillB -> detail-panel third slot).
    for i, (base, kit) in enumerate(PASSIVE_SKILLS.items()):
        sid = "S_%d_1" % (9701 + i)
        passive_skill = {
            "name": kit.get("name", "被動"),
            "skill": kit["skill"],
            "skillUp": kit.get("skillUp", [0, 0]),
            "info": kit.get("info", ""),
        }
        if isinstance(kit.get("pl"), list):
            passive_skill["pl"] = list(kit["pl"])
        skills[sid] = passive_skill
        for aid, entry in merged.items():
            if aid.rsplit("_", 1)[0] != base:
                continue
            # Only the 6★ form gets the passive slot; the 5★ purple card
            # keeps just 英雄技 + 隊長技.
            try:
                _passive_star = int(aid.rsplit("_", 1)[1])
            except (IndexError, ValueError):
                _passive_star = 0
            if _passive_star < 6:
                continue
            pl = entry.get("pl")
            if isinstance(pl, list):
                while len(pl) < 14:
                    pl.append("")
                pl[13] = sid
    # ---- high-tier heroes: default third (passive) skill ----------------
    # The client's detail panel shows 英雄技 / 隊長技 / 被動技能 when pl[13]
    # is non-empty.  Give every high-tier family a data-driven placeholder;
    # explicit PASSIVE_SKILLS entries above take precedence.
    _high_families = {
        base for base, _tier in _gallery_tier_map().items()
        if _tier == "high"
    }
    if _high_families:
        _high_passive_sid = "S_9700_1"
        skills[_high_passive_sid] = {
            "name": "被動",
            "skill": [["passive", 0]],
            "skillUp": [0, 0],
            "info": "被動技能（待設計）。",
        }
        for aid, entry in merged.items():
            if aid.rsplit("_", 1)[0] not in _high_families:
                continue
            # 5★ purple cards have no passive slot; only 6★ gets the third
            # (被動技能) button.
            try:
                _passive_star = int(aid.rsplit("_", 1)[1])
            except (IndexError, ValueError):
                _passive_star = 0
            if _passive_star < 6:
                continue
            pl = entry.get("pl")
            if isinstance(pl, list):
                while len(pl) < 14:
                    pl.append("")
                if not pl[13]:
                    pl[13] = _high_passive_sid
    # 2026-10-23: numeric summary for the 詳情 page (the normal skill info
    # text stays free of numbers).
    for _sid, _sk in skills.items():
        if isinstance(_sk, dict):
            _sk["detail"] = _skill_detail_text(_sk)
    # Passive trigger condition consumed by AvatarData.skill_diff.
    for aid, entry in merged.items():
        if not isinstance(entry, dict):
            continue
        diff = SKILL_DIFF.get(aid.rsplit("_", 1)[0])
        if diff:
            entry["skill_diff"] = int(diff)
    for name_map in (HERO_NAMES, UNIT_NAMES):
        for base, name in name_map.items():
            for aid, entry in merged.items():
                if aid.rsplit("_", 1)[0] == base:
                    entry["name"] = name
    # 極限突破 materials use a different name per star
    # (3★ 靈眷秘寶 / 4★ 天眷秘寶 / 5★ 神眷秘寶).
    for aid, name in STAR_MATERIAL_NAMES.items():
        if aid in merged:
            merged[aid]["name"] = name
    _apply_skill_tier_rules(merged, skills)
    _apply_summon_rules(merged, skills)
    return merged


def _altar_exchange_cfg():
    """VIP altar score shop (PanelInteGralExchange).

    User rows (2026-10-22):
      6★ 技能餅乾     100 分
      6★ 魔法藥水     100 分
      5★ 脫縛         200 分
      5★ 神眷秘寶     250 分
      6★ 莫德凱撒    1200 分
      6★ 渡厄        1200 分
    """
    # 2026-10-25 user ordering: heroes first, then materials grouped by
    # category with quality low -> high, star-up materials last.
    return [
        # ---- heroes (6★, 1200 points) ----------------------------------
        [{"avatar": {"A_1137_6": 1}}, 1200],   # 莫德凱撒
        [{"avatar": {"A_1209_6": 1}}, 1200],   # 兔寶寶提莫
        [{"avatar": {"A_1036_6": 1}}, 1200],   # 伊莉絲
        [{"avatar": {"A_1310_6": 1}}, 1200],   # 鋼鐵俠提莫
        [{"avatar": {"A_1216_6": 1}}, 1200],   # 聯盟之喙艾尼維亞
        [{"avatar": {"A_1079_6": 1}}, 1200],   # 費德提克
        [{"avatar": {"A_1099_6": 1}}, 1200],   # 圖奇
        # ---- 技能餅乾 (small -> large) ---------------------------------
        [{"avatar": {"A_2107_4": 1}}, 20],     # 技能餅乾-小
        [{"avatar": {"A_6992_5": 1}}, 45],     # 技能餅乾-中
        [{"avatar": {"A_6992_6": 1}}, 100],    # 技能餅乾-大
        # ---- 魔法藥水 (small -> large) ---------------------------------
        [{"avatar": {"A_6993_4": 1}}, 17],     # 魔法藥水-小
        [{"avatar": {"A_6993_5": 1}}, 50],     # 魔法藥水-中
        [{"avatar": {"A_6993_6": 1}}, 100],    # 魔法藥水-大
        # ---- 經驗材料 ---------------------------------------------------
        [{"avatar": {"A_6996_5": 20}}, 100],   # 武鬥密卷-中 ×20
        # ---- 神眷秘寶 ---------------------------------------------------
        [{"avatar": {"A_6999_5": 1}}, 250],
        # ---- 升星材料 (2★ -> 6★, last) ---------------------------------
        [{"avatar": {"A_6004_2": 1}}, 10],     # 2★ 聚元
        [{"avatar": {"A_6022_3": 1}}, 30],     # 3★ 破障
        [{"avatar": {"A_6076_4": 1}}, 100],    # 4★ 啟迪
        [{"avatar": {"A_6075_5": 1}}, 200],    # 5★ 脫縛
        [{"avatar": {"A_6994_6": 1}}, 1500],   # 6★ 渡厄（1200→1500）
    ]


def _medal_avatar_exchange_cfg():
    """Medal shop avatar rows: 6★ ADVANCED heroes only (user rule 2026-10-22).

    The user trimmed the medal shop to six-star advanced heroes and asked
    for no discounted rows.  Every row is full price (1000 medals).
    """
    tier_map = _gallery_tier_map()
    out = {}
    for aid, meta in AVATAR_CATALOG.items():
        if int(meta.get("kind", 1) or 0) != 1:
            continue
        base = aid.rsplit("_", 1)[0]
        if tier_map.get(base) != "advanced":
            continue
        try:
            star = int(meta.get("star", 0))
        except (TypeError, ValueError):
            continue
        if star != 6:
            continue
        if len(aid.split("_")) != 3:
            continue
        out[aid] = 1000
    return out


def _medal_equip_exchange_cfg():
    """Medal shop equipment rows.

    User rule (2026-10-22): all equipment is removed from the medal shop.
    """
    return {}


def _medal_cycle_cfg():
    """Featured/discounted medal rows removed (user rule 2026-10-22).

    PanelCenterShopVIP.infoUIsC() unconditionally reads cycle_exchange[0]
    and divides by its length, so keep one info-only row with no purchasable
    entries instead of returning an empty array (#1010 otherwise).
    """
    return [{"info": "勳章兌換：僅限六星進階英雄。"}]


# VIP 0-15 experience ladder.  Index lv holds the exp required for the step
# lv -> lv+1 (the client's getVipEXP(lv) sums entries 1..lv-1, i.e. the
# cumulative requirement to reach level lv).  Thresholds:
#   VIP1 0, VIP2 100, VIP3 500, VIP4 1000, VIP5 2000, VIP6 5000,
#   VIP7 10000, VIP8 20000, VIP9 50000, VIP10 100000, VIP11 200000,
#   VIP12 500000, VIP13 1000000, VIP14 2000000, VIP15 5000000.
_VIP_STEP_EXP = [0, 100, 400, 500, 1000, 3000, 5000, 10000, 30000, 50000,
                 100000, 300000, 500000, 1000000, 3000000, 0]


def default_cfg():
    """Minimal server config the client needs before it will show the lobby.

    Shape/field names come straight from Game.re_configSet / initConfig.
    Values are harmless defaults until the real ones are recovered.
    """
    _refresh_up_rotation()
    cfg = {
        # GlobalData.$mConfig_client.* -- every key the client dereferences
        "client_config": {
            # is_vip drives checkIOSvip(): when set the client pops a
            # "buy VIP" dialog after every coin purchase on desktop.  VIP
            # levels themselves come from user.vip_lv, so keep this off.
            "star_id": [], "is_vip": 0, "bbs_url": "",
            "help_url": {}, "pf_bbs_url": {}, "pf_comment_url": {},
            "app_update_url": "", "award_code": "", "banner_ad": 0,
            "pay_fun_30": 0, "self_login": 0,
            # PanelActivityFund.setUIs() picks an illustration by fund
            # status (buy period vs claim period).  The original art is not
            # in the extracted atlases, so reuse the shop backdrop.
            "fund_avatar": {"avatar": ["UI_shop_bg", "UI_shop_bg"]},
            # PanelActivityGamble appends "" + gamble_avatar and passes it to
            # createImage(); reuse an existing illustration texture.
            "gamble_avatar": "UI_shop_bg",
        },
        "system_simple": {
            "ana_key": "",
            # Game.initConfig() maps these directly onto GameMapConfig:
            # [0] ROUND_MAX, [1] LINE_POS (lane length in pixels),
            # [2] MIN_SPACE_POS, [3] SUMMON_POS, [4] MAX_POS_PER,
            # [5] sudden-death round.  Keep the client defaults; a small
            # LINE_POS or a large MAX_POS_PER scrambles movement/positions.
            "battle": [30, 3000, 200, 500, 0.35, 30],
            # Game.initConfig() maps [0..8] onto the Avatar combat constants:
            # MIN_DAMAGE_RATE, REAL_DAMAGE_RATE, SIGN_DAMAGE_RATE, CRIT_RATE,
            # MISS_POINT, CRIT_POINT, MISS_MAX, CRIT_MAX, DANGEROUS_RATE.
            # [9..16] feed the hit/crit/reduction formulas, [14] lifesteal,
            # [17] burn, [18] poison, [19] sudden-death, [20] heal/bless,
            # [21] the final damage multiplier in Avatar.injured().
            # Missing entries silently produce 0 damage, so keep 0..23.
            "attack": [0.1, 0.3, 1.5, 2, 20, 20, 60, 80, 0.5,
                       100, 100, 100, 100, 100, 0.3, 1, 100,
                       0.05, 0.02, 0.05, 0.2, 1, 1, 1],
            # Game.initConfig() maps [0..8] onto Avatar.POWER_*; the client
            # defaults are the intended values.  [9]/[10] are used by
            # Avatar.getPower(), [11]/[12] by SkillSet.getPower().
            "power": [1e-8, 0.5, 2, 0.625, 0.625, 1000,
                      0.1, 0.1, 0.5, 0.5, 2, 0.5, 0.1],
            "culture": {},
            # GlobalFunction.getLeaderShip(): floor(leadership[0]*lv + leadership[1])
            # 2026-10-21: at lv60 this gives 299 + VIP 1 = 320 (five 7★
            # heroes at 58, potion floor 48 → 240 + 80 reserve).
            "leadership": [4, 79],
            # [17] gates center_scence, which is the 神秘商店 / 战魂 panel
            # (PanelCenterSoul).  Keep it open at an early level; the guide
            # helper marks M16_1..M16_5 done so addList_Shop's checkGuide()
            # returns immediately without needing guide scripts.
            # index 6 is status_pve_hard.  The client's hard tab builds its
            # list before creating mList_h and #1010s on first open, so keep
            # it locked until that panel path is fixed; normal mode has all
            # ten chapters.
            # 2026-10-24: index 6 (困難副本) is now open; index 11
            # (PVP 碎片/裝備碎片) stays locked permanently, but index 17
            # (center_scence / 神秘商店) must stay open — locking it removed
            # the 神秘商店 building from the lobby after a ranked match.
            "start_lv": [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 999, 0, 999,
                         0, 0, 0, 0, 0, 0, 0],
            # Avatar.getPhaseType/getPhaseList index this by avatar type
            # (1 = A_1xxx story heroes, 2 = A_2/3/4xxx) and star.
            # Entry = [material count, max phase, lv bonus/phase,
            #          pith/phase, leadership/phase].
            # Phase-up material is a DUPLICATE of the same avatar id
            # (AvatarData.phaseUpList / PanelStarUpStart.setUIList).
            "phase_config": [
                {
                    # 2026-10-21 star-up gate rules:
                    #   2★ 0阶 -> 3★ (direct), 3★ 1阶 -> 4★,
                    #   4★ 2阶 -> 5★, 5★ 2阶 -> 6★, 6★ 3阶 -> 7★.
                    # getPhaseType() offers phase-up while phase < max,
                    # then the star-up panel opens.
                    "2": [1, 0, 5, 10, 1],
                    "3": [1, 1, 6, 15, 1],
                    "4": [1, 2, 8, 20, 1],
                    # 2026-10-25: 5★ phases keep +10 virtual levels but no
                    # longer grant pith, so 5★满阶 stays below 6★0阶满级
                    # (the old 25/阶 pith made its DEF beat 6★0).
                    "5": [1, 2, 10, 0, 1],
                    # 6★ has three 阶; phase 3 unlocks the final 7★ star-up.
                    # No virtual level bonus now (the independent limit break
                    # raises the real level cap to 100); each 阶 gives pith
                    # and leadership.
                    "6": [1, 3, 0, 30, 1],
                },
                {
                    "1": [1, 2, 3, 5, 0],
                    "2": [1, 3, 4, 8, 0],
                    "3": [1, 4, 5, 10, 0],
                    "4": [1, 5, 6, 12, 0],
                    "5": [1, 6, 8, 15, 0],
                },
            ],
            # PanelDetailDN.getDNAttrsAllValue() reads dn[5] unconditionally
            # 德諾之陣 (PanelCenterDNTeam / PanelDetailDN).
            # dn[key] = [nameLangId, prerequisiteKey, unlockLv, unlockStone,
            #            stonePerLevelFactor, attrType, basePct, pctPerLevel]
            # User state attrs.dn[key] = [dnlv, avatarKey, ...].
            "dn": {
                "1": [25046, None, 15, 50, 5, "hp", 0.005, 0.005],
                "2": [25047, "1", 16, 60, 5, "hp", 0.005, 0.005],
                "3": [25048, "2", 17, 70, 6, "ap", 0.005, 0.005],
                "4": [25049, "3", 18, 80, 6, "ap", 0.005, 0.005],
                "5": [25050, "4", 19, 90, 7, "de_ph", 0.005, 0.005],
                "6": [25051, "5", 20, 100, 7, "de_ph", 0.005, 0.005],
                "7": [25052, "6", 21, 110, 8, "de_ma", 0.005, 0.005],
                "8": [25060, "7", 22, 120, 8, "de_ma", 0.005, 0.005],
                "9": [25054, "8", 23, 130, 9, "hit", 0.004, 0.004],
                "10": [25055, "9", 24, 140, 9, "flee", 0.004, 0.004],
                "11": [25056, "10", 25, 150, 10, "crit", 0.004, 0.004],
                "12": [25057, "11", 26, 160, 10, "tough", 0.004, 0.004],
                "13": [25058, "12", 28, 200, 12, "all", 0.008, 0.008],
            },
            "vip_config2": [],
            # assorted arrays the lobby panels index into directly
            # open_status == 1 makes PanelCenterMain create the 签到 building
            # (mBtn_checkin -> PanelEveryDaySign, the monthly sign-in board).
            "check_in": dict({"open_status": 1}, **_check_in_cfg()),
            "radio": [0, 0, 0, 0, 5, 5],     # LOL_TeamSet.show_TextPop -> [4],[5]
            "chat": {"open_status": 0},
            # 祭坛/角色抽奖 (PanelCasinoA/B):
            # [0]/[1] coin cost for 1/10 draws, [2]/[3] score cost for 1/10,
            # [10] sale flag, [11] medal on a free draw,
            # [12]/[13] medal on paid 1/10 coin draws,
            # [14] paid single coin draws before one is free (display uses
            #      count % ([14]+1); see PanelCasinoA), [15] score free cap.
            # 2026-10-22: no discounts, no timed free-draw reset reward.
            # Ten-draws cost exactly 10x the single price; [15]=0 removes
            # the score free-draw quota and [14] is effectively unreachable.
            "wager_avatar": [100, 1000, 1000, 10000, 0, 0, 0, 0, 0, 0,
                             -1, 1, 2, 20, 999999, 0, 0, 0, 0, 0],
            "wager_free": [0, 0],
            # Featured avatars on the 祭坛 tab (PanelCenterShopVIP.setCasinoUI
            # reads [0][0], [1][0] and [2]).
            "show_avatar": [
                ["A_1001_2", "A_1012_4", "A_1013_3"],
                ["A_1002_2", "A_1003_2", "A_1004_2"],
                "A_1005_2",
                # PanelActivityGrouponBuy indexes [3][0]/[3][1] for its two
                # purchase-case illustrations.
                ["A_1005_2", "A_1001_2"],
                # PanelCasinoVIP draws its single/ten buttons from [4].
                # 2026-10-24: rotates every 48h at 04:00 (see _UP_ROTATION).
                [_UP6, _UP6],
            ],
            # Guide/assistant illustrations used by PanelAwardTips (the
            # golden reward bar reads [0]) and the intimacy popups ([16]/[17]).
            # 艾琳教官 = A_1999_6; without this the bar has no portrait.
            # [6] is the portrait in the 遠征 info box (gallery hero #11 普朗卡).
            # A_1011 has only 3★-5★ art, so use the highest real card.
            # [7] is the post-expedition award panel portrait (white circle).
            "show_id": (["A_1999_6", "", "", "", "", "", "A_1011_5",
                         "A_1011_5"]
                        + [""] * 8
                        + ["A_1999_6", "A_1999_6"] + [""] * 12),
            # PanelEquipChange/ItemEquipSelect index star tables with
            # equip_al, and Equip.getStep() reads star_lv.
            # 裝備煉化 (alchemy).  phase key = (baseStar + alchemy[1]) +
            # "_" + alchemy[0]; value = [rate0, rate1, gold].  The client
            # compares keys as strings, so every star tier must exist.
            "equip_alchemy": {
                # 4★ is the first tier that gets the alchemy frame overlay.
                # Equip.getRes() computes
                #   box = alchemy[0] + (alchemy[1] + star - equip_al) * 3 - 1
                # and only UI_equip_box_0000..0005 exist.  With equip_al=1,
                # 2-3★ equipment hit boxes 2/5 (red) although their own green
                # frame is already part of the icon art; 4★+ then ran past
                # the available textures.  equip_al=4 makes 1-3★ use the
                # artwork frame and reserves the overlay for 4★ alchemy.
                "open_status": 1, "equip_al": 4, "star_lv": 7,
                # [mainStatRate, atkRate, goldBase].  PanelEquipAlchemyStart
                # calls nextEquip() and looks up "<star>_<level>" for the
                # preview.  2026-10-22: alchemy again raises main stats.
                # The client returns the target step's rate directly:
                #   6★ +1 = 1.10, +2 = 1.20, final 7★ (key 7_3) = 1.30.
                "phase": {
                    "%d_%d" % (star, q): [
                        (1.0 + 0.10 * q) if star == 6
                        else (1.30 if (star == 7 and q == 3) else 1.0),
                        (1.0 + 0.10 * q) if star == 6
                        else (1.30 if (star == 7 and q == 3) else 1.0),
                        100 * star + 200 * q,
                    ]
                    for star in range(1, 9)
                    for q in range(4)
                },
            },
            # Equip formulas (Equip.getHpMax/getPoint/getWashCoin/...):
            # [0]=inventory cap, [1]=per-level stat growth, [2]=point base,
            # [3]=point bonus, [7]=wash mark, [8..9]=wash coin,
            # [10]=sell-mark divisor, [12]=rise cost factor, [13]=vip gate
            # [2] was the shared star*level auto-point base.  The new crit
            # system uses fixed secondary stats, so it is zero: equipment
            # level no longer grants hit/flee/crit/tough.
            # [1] linear growth per level; [2]/[3] old potential model (now
            # replaced by the 255-click affix wash); [4] forge cubic is tiny
            # so a level-150 item is affordable; [5] base forge cost.
            # [8]/[9]: 點券 wash cost per click = 90 flat (ten clicks = 900).
            # The old 60 + 5*star formula showed 95 on alchemised 6★ gear
            # (effective star 7), so the per-star term is zeroed.
            "equip_config": [500, 0.1, 0, 0, 0.000001, 0.1, 0.5,
                             10, 90, 0, 4, 0, 1, 0] + [0] * 16,
            # 2026-10-25: PanelCenterTaskAward builds the "已領取/領取" pay-gift
            # row when this array has more than one entry.  Keep a single
            # element so the row disappears while checkTaskComplete() can
            # still read pay_gift[0] safely.
            "pay_gift": [1000],
            "score_config": [0, 0, 999999],
            # getEnergy(): [0]=base, [1]=per level, [2]=minutes per regen,
            # [3]=cap, [4]=extra
            # [0] base, [1] per level, [2] regen minutes, [3] cap,
            # [4] coin base cost, [5] max purchases, [6] unused,
            # [7] coin increment per purchase, [8] sale flag.
            "energy_config": [100, 0, 5, 200, 50, 10, 0, 50, 0, 0],
            # [3] is the per-PVP fragment-energy threshold, [4] max buys,
            # [5] cost increment, [6] base coin cost.
            "capacity_config": [100, 5, 1, 1, 10, 10, 100, 0] + [0] * 12,
            # getCurrLvMaxEXP(): exp_config[0]*lv^2 + [1]*lv + [2],
            # levels >= [3] need no exp.  2026-10-25: summoner max level 60
            # (25->60 costs 147,000 exp; story stages give ~74% of that).
            "exp_config": [0, 100, 0, 60],
            # getCurrLvMaxEXP() reads up_exp[lv + 1]
            "up_exp": [0] * 200,
            # PanelBottomMain.openPrompt() reads zone_boss.open_status;
            # checkBossIsOpen()/checkBossInGuideTime() read the other fields
            # 遠古大龍 / 世界Boss: open all day so the tab is usable.
            "zone_boss": {"open_status": 1, "open_times": [[0, 0]],
                          "max_alive_time": 1440,
                          "predict_alive_time": 1440,
                          # checkBossInDelay()/checkBossIn() index [0]/[1];
                          # both zero disables the random spawn delay.
                          "delay_times": [0, 0],
                          # PanelBossBattle reads these when the player is
                          # waiting to revive: minutes until revival is
                          # allowed and the normal/super revive windows.
                          "min_relive_time": 60,
                          "relive_time": 300,
                          # Fraction added to damage for super revive.
                          "super_relive": 0.5,
                          # Seconds between automatic refresh polls.
                          "report_timer": 10,
                          # PanelBossEnd/PanelBossList iterate kill_gifts.
                          "kill_gifts": [],
                          # checkIsSale("center_boss") reads [2].
                          "relive_coin": [10, 20, 30]},
            # isTeamItemUnlock()/isTeamUnlock() index these arrays directly
            "unlock_avatar": [0] * 10,
            "unlock_team": [0] * 10,
            # GuideTools.getCanEquipList() reads equip_show.length
            "equip_show": [0] * 10,
            # PanelBottomMain.callButton() reads extreme.open_status
            "extreme": {"open_status": 0, "time": {}, "gambling": [],
                        "flower": [], "flower_times": [], "grant_gift": [],
                        "battle_gift": [], "flower_gift": [], "aud_gift": [],
                        "change_team": 0},
            # [2] = max attainable VIP level, [3] = highest shown level.
            # [4] is checked for null before zone_config[id][1] is used as a
            # Date, so keep it None.  16 rows (VIP0-15) like the master build.
            "vip_config": [0, 1, 15, 15, None],

            # ---- remaining system_simple fields the UI reads -------------
            # (scanned from the decompiled AS3; shapes are "safe empty")
            "BattlePVP_line": [],
            # GameMapManager.getPVPData picks a random KEY from pvp_line and
            # reads pvp_line[key] = [nameLangId, lane, pos1, pos2].
            "pvp_line": {"0": [92010, ["mg001", "mg002", "mg003"],
                               0.85, 0.85]},
            "frag_line": [],
            "activity_show": 0,
            # GameMapData.getDiffConfig() returns combat_diff[diff]:
            #   [0] multiplies hpMax/ap/dePh/deMa, [1] multiplies
            #   hit/flee/crit/tough, [2..4] are exp/gold/energy rates.
            # [0]/[1] MUST be > 0: with 0 every combatant spawns with 0 HP
            # and 0 attack, the fight can only time out into a loss.
            # 2026-10-24: hard mode copies the normal monsters but scales
            # enemy HP/attack/defence ×1.8 and secondary stats ×1.35.  The
            # client only applies this to server-provided team2 units, so the
            # player's own team is unaffected.  2026-10-25: hard mode's
            # exp/gold rates are 2 so the stage cards and settlement panel
            # show exactly what the server grants (it doubles both on hard).
            "combat_diff": [[1, 1, 1, 1, 1, 0],
                            [1.8, 1.35, 2, 2, 1, 0],
                            [1, 1, 1, 1, 1, 0],
                            [1, 1, 1, 1, 1, 0]],
            # Avatar level curve (Avatar.getNextExp/getAllExp):
            #   nextExp(lv) = expRate * (a*lv^2 + b*lv + c)
            # `provide_exp[star-1]` multiplies the accumulated EXP a swallowed
            # avatar passes on; every material also adds avatarData.offerExp
            # (tl[6], 100 for our catalog) on top.
            "avatar_exp": [10, 20, 30] + [0] * 97,
            "provide_exp": [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            # Avatar.PITH_POINT: each point of hp/ap/de_ph/de_ma percent in
            # user.avatars is worth this many flat stat points.  The 培养
            # panel (PanelBetterStart/PanelAvatarFoster) also reads culture.*.
            "culture": {
                "culture_lv": 1,
                "culture_pith": 1,
                "max_pith": 9999,
                # Must be > each avatar's current pith; otherwise
                # PanelAvatarFoster treats every avatar as capped, pops the
                # 90678 warning and never calls user.avatar_culture.
                "max_pith_base": 9999,
                "sale": 0,
                # ItemAvatarFoster.checkLock() uses indexOf(star), so this is
                # the list of fosterable star levels (not a minimum).
                # 2026-10-24 user rule: 角色培養 temporarily closed.  No hero
                # has 8★, so PanelDetailAll greys the 培養 button and the
                # click handler shows 90645 ("此功能暫未開放").
                "avatar_culture": [8],
                "price": {"coin": {"1": 50, "10": 450},
                          "culture_book": {"1": 1, "10": 9}},
            },
            # [0]=base, [1]=increment per purchase, [2]=coin cost,
            # [3]=absolute cap (plus the VIP bonus).  Offline test server:
            # the warehouse cap is 2000.
            "avatar_len": [200, 10, 200, 2000] + [0] * 16,
            "friend_len": [50, 5, 100, 100] + [0] * 16,
            "friend_cd": [0, 0, 0],
            "dn_lv": 10, "equip_multiple": 1,
            # PanelChip.addList() clones this into a typed Array
            # Fragment ids shown even at 0/0 in the chip panel (short form:
            # last segment = number of pieces required).
            # 2026-10-24: 裝備碎片系統已屏蔽，不再顯示任何碎片。
            "fragment_keep": [],
            # Per-slot forge/rise cost multiplier.  Equip.getRiseGold() and
            # getAlchemyGold() do NOT look up "a<type>" directly: they first
            # translate the type through {a1:0,a2:0,a3:1,a4:2,a5:3} and then
            # index equipspace_gold with the resulting NUMBER.  The config
            # must therefore be a dense Array indexed 0..3 (type 1/2 -> 0,
            # type 3 -> 1, type 4 -> 2, type 5 -> 3), not an object keyed
            # "a1".."a6".  With an object every lookup was undefined ->
            # NaN -> Tools.toInt() == 0, so the rise price showed 0 and the
            # 鍛造 button stayed disabled.
            "equipspace_gold": [1, 1, 1, 1],
            "equipstar_gold": [100, 200, 400, 800, 1600, 3200,
                               6400, 12800, 25600, 51200],
            # [0]=fallback halo exp base, [1]=fallback growth,
            # [2]=mark->points per wash, [3]=coin->points per wash,
            # [4]=attr per halo lv, [5]=cap, [6..9]=washes required for
            # halo lv 1->2, 2->3, 3->4, 4->5.
            # Halo has five levels: white (base lv1), green, blue, purple,
            # orange.  Each level grants +20% of the equipment's base stats
            # (Equip.getHaloUpAttrs() = 1 + equipwash[4] * haloLv), so the
            # orange halo is +100%.  Either currency counts as one wash and
            # surplus points carry into the next bar.
            "equipwash": [100, 1.2, 1, 1, 0.2, 5, 22, 47, 77, 109] + [0] * 10,
            # Forge crit tiers: normal +1, crits +2/+3/+5/+10.  The client
            # reads these keys to animate the gain.  Include 1..10 so a crit
            # clipped by the level cap (e.g. +10 -> +4 at max) still animates.
            "equip_multiple": {str(i): i for i in range(1, 11)},
            "equip_rise_crit": {"2": 0.08, "3": 0.04, "5": 0.015,
                                "10": 0.005},
            "everyday_gifts": {"start_lv": []},
            "exp_multiple": {},
            # 探險 (PanelActivityExploration): unlock_lv gates the tab,
            # map_max is the number of stages shown.
            "explore": {"unlock_lv": 1, "map_max": 10,
                        "team_max": 3, "leadership_max": [10, 50],
                        # GameMapManager.getExplorationData() reads
                        # explore.line[1] as the background pool and builds
                        # line = [1, [random background]].
                        "line": [1, ["mg001", "mg002", "mg003"]],
                        # box_kind[n] 0 = normal chest, 1 = battle chest
                        "box_kind": {str(n): (0 if n % 3 else 1)
                                     for n in range(20)},
                        # Free team refreshes, then coin price; the mode
                        # reroll price is price = [0]*n + [1].
                        "free_times": 3, "refresh_price": 20,
                        "refresh_mode_price": [10, 50],
                        "relive": [10, 20, 50], "relive_vip": 0},
            "fragment_pk": [0] * 20,
            # PanelFunctionOpenInfo.init() does `arr =
            # guide_start_lv[lv]` with `arr:Array`.  A numeric 0 raises
            # #1034 (cannot convert 0 to Array); null makes the panel skip
            # the optional "new functions" list.
            "guide_start_lv": [None] * 100,
            "init_gift": {"equip": []},
            "initialize_avatar": [], "initialize_info": {},
            "lose": [[0], [0], [0], [0]],
            # [max love level, threshold growth, base threshold, leadership
            # reduction per level].  Avatar.getLoveList() turns love_exp into
            # levels; each level lowers 統御值 by love_up[3].  Magic potions
            # grant 100/300/600 love_exp at 4★/5★/6★ (LOVE_POTION_GAIN),
            # so 4★ reaches level 1, 5★ level 2 and 6★ level 3.
            "love_up": [5, 100, 100, 1] + [0] * 6,
            "medal_fun": 0, "mon_card": {},
            "msg_config": [[], []],
            "pay_first_gift": {},
            "pf_comment_lv": [0, {}],
            # getPVPoutputMark(): (K/(rank+offset))^pow + base, times the
            # per-rank multiplier below.
            "pvp_config": [0, 0, 0, 0, 0, 0, 1000, 10, 0.5, 1] + [0] * 10,
            "pvp_get_mark": [1.0] * 100,
            # Cross-server ranked PVP (排位赛 / 巔峰之戰).  See the full
            # definition below; this key is overwritten by the later one.
            "cross_pvp": {"open_status": 1,
                          "cross_server_pvp": [0, 60, datetime.datetime.utcnow(),
                                               7, 0]},
            "random_battle": [0] * 10,
            "reload_time": datetime.datetime.utcnow(),
            "rename": 0,
            # [3] = max skill level, [5] = gold cost factor
            "skill_book_exp": [0, 0, 0, 10, 0, 10] + [0] * 4,
            "skill_book_rand": [0] * 10,
            # PanelBetterStart: skill0 lv cap = slv_config[0]; [1] is the
            # skill-point conversion rate used by getSkillProbability():
            #   p = floor(points * rate / ((skill_lv + 1) * star) * 100)
            # Skill level cap is 10.  [1] still feeds the legacy hero-material
            # point formula in getSkillProbability; the 164/5★249/6★249
            # cookies use their direct skillup percentages (10/20/40).
            "slv_config": [10, 0.05, 0, 0, 0, 0, 0, 0, 0, 0],
            # ItemAvatarSoul/ItemEquipSoul/LOL_Detail* read this from
            # system_simple (NOT the top-level config key).
            "soul_exchange": {
                "avatar": {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6},
                "equip": {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7},
            },
            # GlobalFunction.formateBetterItemsError() warns when a fed unit's
            # star is >= this value; 0 made every material (even 1★) pop the
            # confirmation.  4 keeps the client's high-star safeguard.
            "star_swallow_tips": 4,
            "talent_avatar": 0, "talent_config": [0] * 10,
            "talent_power": [0] * 10,
            "task_money_rate": 1,
            "vip_avatar": [0] * 20, "vip_gift_diff": 1, "vip_tips": [],
            # PanelMaze builds its left-hand activity tabs from this list.
            # 2026-10-24 user request: 野区 keeps only 遠征.
            "wild_area": ["expedition"],
            # 英雄圖鑑: ordered card ids, novice -> advanced -> 7 UP heroes.
            "hero_gallery": _hero_gallery_list(),
            "win": ["1", "1", "1", "1"],
            # PanelCenterPVP.tabBar_CREATION_COMPLETE() reads
            # cross_server_pvp[1] as the fragment-energy cost, [2] as the
            # season anchor Date, [3] cycle days and [4] the lock window in
            # hours before a cycle ends.  0 = the tab is always open.
            "cross_pvp": {
                "open_status": 1,
                "cross_server_pvp": [
                    0, 60,
                    datetime.datetime.utcnow() - datetime.timedelta(days=1),
                    7, 0],
                # (K/(rank+offset))^pow+base is the bot win-count formula in
                # ItemPVPRankList.
                "server_pvp_robotrank": [1000000, 100, 1, 3],
                "robot_lv": 0,
                "hide_team": {},
            },
            # GameMapManager.getBattleOfThePeak(): random entry is indexed by
            # a random key, then line = [2, entry[1], entry[2], entry[3]].
            # entry[1] is the per-line background list used by BgLayer.
            "BattlePVP_line": [
                [98060, ["mg001", "mg002"], 0, 0],
                [98061, ["mg002", "mg003"], 0, 0],
                [98062, ["mg003", "mg001"], 0, 0],
            ],
            # tear is indexed by equipment type: weapon->0, armour->1,
            # accessory->2, boots->3.  All four rows must exist because
            # Equip.getSellDust() indexes dust.tear[type-2] (boots = 3).
            "dust": {"symp": [[0, 0, 0, 0], [0] * 10],
                     "tear": [[0] * 10, [0] * 10, [0] * 10, [0] * 10],
                     "return": 0,
                     # LOL_MagicButton 用 max[mIndex]；四色都要有值。
                     # 0=綠色生命1200, 1=藍色攻擊800,
                     # 2=紫色生命3600, 3=橙色攻擊2400.
                     # 2026-10-25: enchant caps scaled x0.35 with the main
                     # stat reduction (same clicks-to-full as before).
                     "max": [420, 280, 1260, 840, 999],
                     "add_magic": [[10, 20, 30, 40, 50]]},
        },
        # ---- guide / tutorial data -------------------------------------
        # GuideMaster's constructor reads guide.battle_guide.battle001 and
        # .combat001; GuideData.monsterId needs an avatar definition it can
        # resolve through AvatarManager, so battle_guide.avatar001 points at
        # the avatar defined below.
        "guide": {
            "def": {},
            "y": {},
            "battle_guide": {
                "avatar001": {"aid": "A_1001_2|0"},
                "avatar002": {"aid": "A_1012_4|1"},
                "battle001": {},
                # GuideMaster assigns this to $gConfig_combat_main and
                # GameMapManager.loadData() builds a GameMapData from every
                # entry, so it must be a complete map record (needs "line").
                "combat001": {"M_000_1": {
                    "name": "新手战斗",
                    "line": [1, ["mg001", "mg002", "mg003"]],
                    "team1": [],
                    # map-lineup form: [aid, lv, slv, line, pos, leader,
                #                   dropRate, dropLv, dropId]
                "team2": [["A_1001_2", 1, 1, 0, 0.8, 0, 0.6, 5,
                           "A_1001_2"]],
                    # victory condition: -1 = 全面取勝 (wipe the enemy team)
                "win": [-1],
                    "energy": 0,
                    "exp": 0,
                    "gold": 0,
                    "limit": [0],
                    "pre": [],
                    "new_4attrs": [0, 0, 0, 0],
                    "equip_drop": [],
                }},
                "user001": {},
                "re0004": {},
                "re0013": {},
                "re0015": {},
                "re0016": {},
                "re0018": {"get_avatars": {}},
                "re0027": {"avatars": {}},
                "re0064": {},
            },
        },
        # ---- avatar catalog -------------------------------------------
        # tl = [signType, actionType, damageType, leadership, lvMax,
        #       expRate, offerExp, offerGold, starUp, sortIndex, skillUpP]
        # pl = [hp0, hp1, ap0, ap1, d10, d11, d20, d21, speed, range,
        #       skill0, skill1, effectSet, skillB]
        # Values copied from AvatarManager.initData() (the client's own
        # single-player fight-test dataset) so they are valid by construction.
        "avatar": {
            # The three story heroes grow with level: hp1/ap1/d1x are the
            # per-level increments used by Avatar.getHpMax()/getDamage().
            # lvMax 30 leaves room for material-fed level-ups across all six
            # chapters (the client's fight-test values stopped at 10).
            "A_1001_2": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [750, 60, 250, 15, 170, 4, 170, 4, 450, 250,
                                "S_1012_1", "S_1002_1", "E_008"]},
            "A_1012_4": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [580, 55, 300, 18, 95, 3, 95, 3, 400, 250,
                                "S_1000_1", "S_1016_1", "E_009"]},
            "A_1028_5": {"tl": [2, 1, 1, 4, 10, 1, 100, 200, []],
                         "pl": [450, 4, 200, 3, 530, 8, 530, 8, 300, 250,
                                "S_1007_1", "S_1015_1", "E_012"]},
            "A_1019_4": {"tl": [3, 2, 2, 4, 10, 1, 100, 200, []],
                         "pl": [990, 12, 297, 3, 100, 2, 100, 2, 350, 750,
                                "S_1006_1", "S_1010_1", "E_018"]},
            "A_1013_3": {"tl": [2, 2, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            # ---- star-up chain (star = third segment of the id) ----------
            # Avatar.getStarUpId() only increments that segment, and
            # isNullNextStarCfgId() requires the next id to exist in cfg.
            # Each step consumes one A_2001_4 material (tl[8]).
            "A_1001_3": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [900, 72, 300, 18, 204, 5, 204, 5, 450, 250,
                                "S_1012_1", "S_1002_1", "E_008"]},
            "A_1001_4": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [1050, 84, 350, 21, 238, 6, 238, 6, 450, 250,
                                "S_1012_1", "S_1002_1", "E_008"]},
            "A_1001_5": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [1200, 96, 400, 24, 272, 6, 272, 6, 450, 250,
                                "S_1012_1", "S_1002_1", "E_008"]},
            "A_1001_6": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [1350, 108, 450, 27, 306, 7, 306, 7, 450, 250,
                                "S_1012_1", "S_1002_1", "E_008"]},
            "A_1012_5": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [696, 66, 360, 22, 114, 4, 114, 4, 400, 250,
                                "S_1000_1", "S_1016_1", "E_009"]},
            "A_1012_6": {"tl": [1, 1, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [812, 77, 420, 25, 133, 4, 133, 4, 400, 250,
                                "S_1000_1", "S_1016_1", "E_009"]},
            "A_1013_4": {"tl": [2, 2, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [828, 78, 240, 17, 636, 6, 120, 4, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1013_5": {"tl": [2, 2, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [966, 91, 280, 20, 742, 7, 140, 4, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1013_6": {"tl": [2, 2, 1, 4, 30, 1, 100, 200, ["A_2001_4"]],
                         "pl": [1104, 104, 320, 22, 848, 8, 160, 5, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1022_5": {"tl": [2, 1, 2, 4, 10, 1, 100, 200, []],
                         "pl": [450, 3, 322, 6, 82, 2, 408, 6, 200, 650,
                                "S_1004_1", "S_1009_1", "E_016"]},
            "A_1029_5": {"tl": [1, 2, 2, 4, 10, 1, 100, 200, []],
                         "pl": [490, 4, 580, 6, 94, 1, 94, 1, 200, 550,
                                "S_1003_1", "S_1017_1", "E_017"]},
            "A_1014_3": {"tl": [1, 2, 3, 4, 10, 1, 100, 200, []],
                         "pl": [600, 4, 300, 6, 94, 1, 94, 1, 360, 500,
                                "S_1008_1", "S_1014_1", "E_002"]},
            "A_2001_4": {"tl": [3, 2, 3, 4, 10, 1, 100, 200, []],
                         "pl": [120, 50, 200, 100, 0, 0, 0, 0, 150, 0,
                                "S_1018_1", "S_1013_1", "E_017"]},
            # ---- daily-sign plant display ids -----------------------------
            # PanelActivitySign builds its plant avatar id as
            # sign_in[k].mcid + str(n+1), so the config key is a prefix
            # ("A_1078_") and the seven day ids below are what it resolves.
            # The icon atlas only ships A_1078_4/5/6, so each day maps its
            # `res` onto one of those; Avatar.resId is all the panel uses.
            "A_1078_1": {"res": "A_1078_4",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_2": {"res": "A_1078_5",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_3": {"res": "A_1078_6",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_4": {"res": "A_1078_4",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_5": {"res": "A_1078_5",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_6": {"res": "A_1078_6",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            "A_1078_7": {"res": "A_1078_4",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
            # n == num still asks for mcid + (n+1), i.e. day 8, on the
            # completed plant; without this id Avatar.init() dereferences a
            # null AvatarData right after the seventh sign.
            "A_1078_8": {"res": "A_1078_4",
                         "tl": [2, 2, 1, 4, 10, 1, 100, 200, []],
                         "pl": [690, 65, 200, 14, 530, 5, 100, 3, 330, 300,
                                "S_1005_1", "S_1011_1", "E_009"]},
        },
        # skill catalog, copied verbatim from SkillSetManager.initData()
        "skill": {
            "S_1000_1": {"name": "菊花三弄", "pl": [1, 3, 500, 0, 0, 1],
                         "skill": [["damage", 0.3, 1, "E_008"],
                                   ["damage", 0.4, 1, "E_008"],
                                   ["weak", 0.8, 3, 9, 2, "E_003"]],
                         "skillUp": [2, 0.1]},
            "S_1001_1": {"name": "連鎖閃電", "pl": [0, 3, 2500, 0, -2, 0],
                         "skill": [["damage", 0.8, 2, "E_017"]],
                         "skillUp": [0, 0.1]},
            "S_1002_1": {"name": "嚇人炸彈", "pl": [3, 15, 2500, 0, 900, 1],
                         "skill": [["stun", 0.5, 3, 2, "E_007"]],
                         "skillUp": [0, 0.1]},
            "S_1003_1": {"name": "魔法連珠", "pl": [2, 4, 1000, 0, 0, 1],
                         "skill": [["combo", 0.3, 2, 5, "E_009"]],
                         "skillUp": [0, 0.1]},
            "S_1004_1": {"name": "生命汲取", "pl": [0, 2, 3500, -0.5, 2, 0],
                         "skill": [["suck", 0.8, 3, 0.7, "E_011"]],
                         "skillUp": [0, 0.1]},
            "S_1005_1": {"name": "奪命飛鉤", "pl": [0, 1, 1500, 0.5, 2, 0],
                         "skill": [["pull", 0.5, 1, 1500, "E_005"]],
                         "skillUp": [0, 0.1]},
            "S_1006_1": {"name": "如來神掌", "pl": [0, 1, 1500, 0, 4, 0],
                         "skill": [["push", 0.5, 1, 500, "E_006"]],
                         "skillUp": [0, 0.1]},
            "S_1007_1": {"name": "野性衝撞", "pl": [0, 0, -500, 0.5, 0, 1],
                         "skill": [["dash", 400, "E_014"],
                                   ["sunder", 0.4, 1, 9, 2, "E_014"]],
                         "skillUp": [0, 0.1]},
            "S_1008_1": {"name": "會心一擊", "pl": [1, 5, 300, -0.5, 0, 1],
                         "skill": [["damage", 3, 1, "E_004"]],
                         "skillUp": [2, 0.1]},
            "S_1009_1": {"name": "治療光環", "pl": [0, 0, 0, 0, 700, 0],
                         "skill": [["cure", 0.1, "E_010"]],
                         "skillUp": [2, 0.1]},
            "S_1010_1": {"name": "淨化之盾", "pl": [1, 4, 0, 0, -1, 1],
                         "skill": [["shield", 0.5, 3, "E_001"],
                                   ["purify", 2, "E_002"]],
                         "skillUp": [2, 0.1]},
            "S_1011_1": {"name": "強力擊暈", "pl": [1, 3, 300, 0, 0, 0],
                         "skill": [["stun", 0.5, 1, 2, "E_005"]],
                         "skillUp": [2, 0.1]},
            "S_1012_1": {"name": "失語打擊", "pl": [0, 4, 300, 0, 0, 0],
                         "skill": [["silence", 0.5, 1, 3, "E_002"]],
                         "skillUp": [2, 0.1]},
            "S_1013_1": {"name": "慢性毒藥", "pl": [0, 0, 1200, 0, 0, 1],
                         "skill": [["poison", 0.3, 3, 0.3, 5, "E_019"]],
                         "skillUp": [2, 0.1]},
            "S_1014_1": {"name": "進化炮臺", "pl": [0, 0, 0, 0, 0, 1],
                         "skill": [["summon", 0.5, "A_2101_4", 2, "E_015"]],
                         "skillUp": [2, 0.1]},
            "S_1015_1": {"name": "真男人", "pl": [2, 10, 0, -0.5, 0, 1],
                         "skill": [["strong", 2, 2, "E_018"],
                                   ["shield", 5, 2, "E_007"]],
                         "skillUp": [2, 0.1]},
            "S_1016_1": {"name": "突然襲擊", "pl": [0, 10, -500, 0, 0, 1],
                         "skill": [["reline", 700, "E_014"],
                                   ["stun", 0.5, 1, 1, "E_007"]],
                         "skillUp": [2, 0.1]},
            "S_1017_1": {"name": "龜派氣功", "pl": [0, 8, 3000, 0, 199, 1],
                         "skill": [["damage", 0.7, 1, "E_013"]],
                         "skillUp": [2, 0.1]},
            "S_1018_1": {"name": "云霜冰箭", "pl": [0, 0, 23500, 0, 40, 1],
                         "skill": [["damage", 10.8, 2, "E_014"]],
                         "skillUp": [0, 0.1]},
            # 裝備6505「神技：天火」的主動技能.  The custom inferno action
            # deals flat true damage to every enemy in all lanes, then applies
            # 1-round curse and 3-round burn.
            "S_9850_1": {
                "name": "三昧真火",
                "pl": [0, 4, 9999, 0, 199, 1],
                # [flat, hpRatio, atkRatio, hitRatio, burnRatio,
                #  burnRounds, evilRounds, fx].  Book levels scale the three
                # percentage coefficients up to 1.8x at level 10; the flat
                # 8000 never changes.
                "skill": [["inferno", 8000, 0.10, 1.0, 1.0,
                           0.10, 3, 1, "e024"]],
                "skillUp": [0, 0],
                "info": "對敵方全體造成真實傷害，詛咒敵方全體1回合，引燃敵方全體3回合。準備0，冷卻4。",
            },
            # 裝備6009「神技：地獄星」的主動技能.  Targets the single
            # lowest-current-HP enemy on the whole battlefield and deals
            # magic damage (defence applies).
            "S_9851_1": {
                "name": "地獄隕落",
                "pl": [1, 3, 9999, 0, 0, 1],
                # [flat, atkRatio, hitRatio, fx]
                "skill": [["hellstar", 8000, 1.5, 0.5, "e_hellfire"]],
                "skillUp": [0, 0],
                "info": "對全場生命值最低的單體造成魔法傷害。準備1，冷卻3。",
            },
            # 裝備6201「魔技：惡魔契約」的主動技能.  Sacrifices 30% of the
            # caster's CURRENT HP, then hits every enemy twice with true
            # damage = flat + lostHP * ratio, and curses them.
            "S_9852_1": {
                "name": "戾伐之償",
                "pl": [1, 2, 9999, 0, 199, 1],
                # [flat, hpLossRatio, hits, curseRounds, fx]
                "skill": [["devilpact", 15000, 1.5, 2, 2, "e024"]],
                "skillUp": [0, 0],
                "info": "減少自身30%當前生命值，對敵方全體造成2段真實傷害，並詛咒敵方全體2回合。準備1，冷卻2。",
            },
            # 裝備6001「狂暴復甦」的被動技能.  No "pl": the client treats a
            # book skill without pl as a passive and applies its first action
            # through Avatar.resetBuff.  The level-1 value is 10% and grows
            # to 30% at book level 10 (參悟).
            "S_9853_1": {
                "name": "生命源泉",
                "skill": [["healup", 0.10]],
                "skillUp": [0, 0],
                # Skill descriptions must NOT contain numeric values: the
                # numbers scale with the skill level, so fixed text would
                # become misleading after upgrades.
                "info": "增加治療與護盾強度。",
            },
            # ---- 2026-10-24 skill-book redesign (user rules).  Active
            # books use custom actions whose coefficient arrays carry the
            # level-1..level-10 range; passive books have no "pl" and their
            # first action is applied by Avatar.resetBuff.
            # 神技：狙殺 (E_6501)
            "S_9854_1": {
                "name": "狙殺",
                "pl": [1, 3, 9999, 0, 0, 1],
                # [atkRatioLV1, atkRatioLV10, fx]
                "skill": [["snipe", 2.0, 3.5, "e_snipe"]],
                "skillUp": [0, 0],
                "info": "對全場生命值最低的敵方單體造成物理傷害。",
            },
            # 神技：突襲 (E_6502)
            "S_9855_1": {
                "name": "幻影突襲",
                "pl": [1, 3, 2500, 0, 0, 1],
                # [dash, radius, h1min,h1max, h2min,h2max, h3min,h3max,
                #  sunderValue, sunderRounds, fx]
                "skill": [["phantomassault", 2500, 900,
                           0.10, 0.20, 0.15, 0.25, 0.20, 0.30,
                           0.10, 3, "e_phantom"]],
                "skillUp": [0, 0],
                "info": "向前突進，對自身周圍最近的敵方單位造成連續三段斬擊，"
                        "並擊破其雙防，持續3回合。若突進後周圍沒有敵人，"
                        "則不發動斬擊。",
            },
            # 神技：湧動 (E_6503)
            "S_9856_1": {
                "name": "力量狂亂",
                "pl": [1, 3, 0, 0, 0, 1],
                "skill": [["strong", 0.45, 3, "e705"]],
                "skillUp": [0, 0],
                "info": "提升自身力量，持續3回合。",
            },
            # 神技：鐵腕 (E_6504)
            "S_9857_1": {
                "name": "護盾猛擊",
                "pl": [0, 3, 800, 0, 0, 1],
                # [shieldRatioLV1, shieldRatioLV10, fx]
                "skill": [["shieldbash", 0.60, 1.20, "e_shieldhit"]],
                "skillUp": [0, 0],
                "info": "對最近的敵方單位造成相當於自身持有護盾值的真實傷害。",
            },
            # 神技：堅定 (E_6506)
            "S_9858_1": {
                "name": "金剛護體",
                "pl": [1, 3, 0, 0, 0, 1],
                "skill": [["steel", 0.20, 3, "e705"]],
                "skillUp": [0, 0],
                "info": "提升自身防禦，持續3回合。",
            },
            # 魔技：獻祭 (E_6010)
            "S_9859_1": {
                "name": "血債血償",
                "pl": [1, 3, 1500, 0, 0, 1],
                # [hpLossRatio, hpDmgMin,hpDmgMax, atkMin,atkMax, rounds, fx]
                "skill": [["bloodpact", 0.30, 0.40, 0.80,
                           0.30, 0.50, 3, "e_bloodpact"]],
                "skillUp": [0, 0],
                "info": "獻祭自身當前生命值，凝聚暗影彈，對範圍內攻擊力最高的"
                        "敵人施加詛咒、虛弱與破甲，持續3回合，並造成魔法傷害。",
            },
            # ---- passive books (no "pl") ----
            "S_9860_1": {
                "name": "兇殘殺戮",
                "skill": [["atkup", 0.10, 0.30]],
                "skillUp": [0, 0],
                "info": "提供大量攻擊力。",
            },
            "S_9861_1": {
                "name": "摧枯拉朽",
                "skill": [["penup", 0.10, 0.30]],
                "skillUp": [0, 0],
                "info": "提供大量物理穿透與魔法穿透，依自身傷害類型生效。",
            },
            "S_9862_1": {
                "name": "固若金湯",
                "skill": [["defup", 0.08, 0.28]],
                "skillUp": [0, 0],
                "info": "提供大量物理防禦與魔法防禦。",
            },
            "S_9863_1": {
                "name": "百發百中",
                "skill": [["hitpct", 0.10, 0.30]],
                "skillUp": [0, 0],
                "info": "提供大量命中。",
            },
            "S_9864_1": {
                "name": "陌影身法",
                "skill": [["fleepct", 0.10, 0.20]],
                "skillUp": [0, 0],
                "info": "提供大量閃避。",
            },
            "S_9865_1": {
                "name": "一擊斃命",
                # [critMin,critMax, critDmgMin,critDmgMax] in percent
                "skill": [["critpair", 0.05, 0.10, 0.10, 0.25]],
                "skillUp": [0, 0],
                "info": "提供大量暴擊與暴擊傷害。",
            },
            "S_9866_1": {
                "name": "逢凶化吉",
                "skill": [["toughpct", 0.05, 0.15]],
                "skillUp": [0, 0],
                "info": "提供大量暴擊抵抗。",
            },
        },
        # PanelServiceMain.changeService() does zone_config["1-01"][0]
        "zone_config": {
            # Open date is also the base for the activity-centre rank
            # schedule (PanelActivityRank starts its first row at the day
            # after zone midnight, so keep it one day in the past).
            # 2026-10-24: two login zones.  一區 uses the main `player`
            # account; 二區 logs into a separate fresh `player_zone2` save.
            "1-01": ["一區",
                     datetime.datetime.utcnow() - datetime.timedelta(days=1),
                     0, ""],
            "2-01": ["二區",
                     datetime.datetime.utcnow() - datetime.timedelta(days=1),
                     0, ""],
        },
        # Six PVP brackets; PanelCenterPVP builds the rank-title table from
        # this array (num = ranks per bracket).  Bot entries returned by
        # user.get_rank_list carry their own data_base, so robot[] stays
        # empty -- the ids are deliberately not "r..." so ItemPVP uses the
        # supplied team instead of looking them up here.
        "pvp_robot": [
            {"num": 100, "name": 92001, "index": 0, "robot": []},
            {"num": 100, "name": 92002, "index": 1, "robot": []},
            {"num": 100, "name": 92003, "index": 2, "robot": []},
            {"num": 100, "name": 92004, "index": 3, "robot": []},
            {"num": 100, "name": 92005, "index": 4, "robot": []},
            {"num": 100, "name": 92006, "index": 5, "robot": []},
        ],
        # 神秘商店 (PanelCenterSoul): timing + refresh cost per tab.
        # updateAvatar() also reads avatar/direction/info — avatar must be a
        # resolvable texture class (otherwise createImage(null) throws #1009).
        "mystery_shop": {
            # 2026-10-24 user rule: all three refresh tiers cost 100 點券.
            "normal": {"start_time": 0, "refresh_interval": 60,
                       "refresh_price": 100, "vip_lv": 0,
                       "avatar": "UI_shop_bg", "direction": 0,
                       "info": 97518},
            "advanced": {"start_time": 0, "refresh_interval": 60,
                         "refresh_price": 100, "vip_lv": 0,
                         "avatar": "UI_shop_bg", "direction": 1,
                         "info": 97519},
            "super": {"start_time": 0, "refresh_interval": 60,
                      "refresh_price": 100, "vip_lv": 0,
                      "avatar": "UI_shop_bg", "direction": 0,
                      "info": 97520},
        },
        # Avatar/equip soul -> shard exchange requirements by star.
        "soul_exchange": {
            "avatar": {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6},
            "equip": {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7},
        },
        # 每日签到 (PanelActivitySign).  checkSignResult() reads
        # sign_in[k].num (days per round) and builds the plant avatar id as
        # mcid + str(n+1).  Completion (n == num) unlocks sign_reward.
        "ploy_system_simple": {
            # 奇遇/活動中心 tabs; gotoOpenActivityPanel indexes [0] and
            # PanelCenterActivity builds the tab bar from this list.
            # 2026-10-24 user rule: 奇遇 keeps only the 任務 tab.
            "fun_control": ["task"],
            # 2026-10-23: PanelPVPGetDayAward reads pvp_rank.time[0] and
            # pvp_rank.lv_range_gift; it used to crash with #1009 when the
            # panel was opened from the arena.
            "pvp_rank": {
                "time": [30],
                "lv_range_gift": {
                    "%d-%d" % (_lo, _lo + 9): {
                        "gold": max(500, 8000 - (_lo // 10) * 800),
                        "coin": max(50, 800 - (_lo // 10) * 80),
                    }
                    for _lo in range(1, 100, 10)
                },
            },
            # 活動中心 → 團購 (PanelActivityGroupBuy).  coin is the single
            # unit price; a ten-pack costs 90%.  item entries are reward
            # wrappers ([0] is the actual reward dict) used both for the
            # banner icons and the random per-purchase grant.
            "groupon": {
                "start_time": datetime.datetime.utcnow()
                - datetime.timedelta(days=1),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=60),
                "duration": 60 * 24 * 60,
                "start_lv": 1,
                "coin": 100,
                "count_range": {
                    "10": {"gold": 1500},
                    "50": {"gold": 8000},
                    "100": {"avatar_soul": {"A_1001_2": 5}},
                },
                "item": [
                    [{"avatar_soul": {"A_1001_2": 1}}],
                    [{"avatar_soul": {"A_1012_4": 1}}],
                    [{"equip_soul": {"E_1001_1": 1}}],
                    [{"equip_soul": {"E_1001_2": 1}}],
                    [{"gold": 500}],
                    [{"culture_book": 2}],
                ],
            },
            # 活動中心 → 競猜 (PanelActivityGamble).  return_coin is indexed
            # by attempt number; the final entry is an unaffordable sentinel
            # because the client reads return_coin[curr+1] before stopping.
            "gamble": {
                "days": 60,
                "radio": [0, 1],
                "return_coin": [[0], [100], [200], [400], [800], [1600],
                                [3200], [6400], [12800], [25600],
                                [999999]],
            },
            # 活動中心 → 福利 (PanelActivityWelfare).  This build runs the
            # dust-exchange branch: each of the four rows buys one of the
            # coloured enchant dusts with gold/coin.  number = -1 keeps the
            # panel out of the original random-jackpot mode.
            "welfare": {
                "start_time": datetime.datetime.utcnow()
                - datetime.timedelta(days=1),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=60),
                "duration": 60 * 24 * 60,
                "buy_offset": 60,
                "start_lv": [1, 0],
                "hue": 0,
                "number_pool": 5,
                "welfare_photo": ["A_1001_2", "A_1012_4", "A_1013_3",
                                  "A_1078_2", "A_1204_6"],
                # free_times[colour] = free single buys per event.
                "free_times": [1, 1, 0, 0],
                # dust_price[colour] = [single, ten]; each maps
                # dustColour -> {currency: price}.
                "dust_price": [
                    [{"0": {"gold": 100}}, {"0": {"gold": 900}}],
                    [{"1": {"gold": 100}}, {"1": {"gold": 900}}],
                    [{"2": {"coin": 20}}, {"2": {"coin": 180}}],
                    [{"3": {"coin": 20}}, {"3": {"coin": 180}}],
                ],
                # setExChangeUIs() calls newAvatarImgById(arr[colour]'s
                # first key), so every row's reward data must be an avatar
                # id mapping (avatar/avatar_soul), never gold/culture_book.
                "reward": [
                    {"avatar_soul": {"A_1001_2": 2}},
                    {"avatar_soul": {"A_1012_4": 2}},
                    {"avatar_soul": {"A_1013_3": 2}},
                    {"avatar_soul": {"A_1078_2": 5}},
                ],
            },
            # 活動中心 → 消費排行 (PanelActivitySpendRank).  fixed_gift keys
            # are cumulative-coin thresholds; struct doubles as the claim
            # reward.  rank_show = [rows above me, rows below me, total].
            "spend_rank": {
                "start_time": datetime.datetime.utcnow()
                - datetime.timedelta(days=1),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=60),
                "duration": 60 * 24 * 60,
                "start_lv": [1, 0],
                "hue": 0,
                # Banner illustration; GameMapTools.newAvatarImgById()
                # dereferences the avatar config entry.
                "show_avatar": "A_1001_2",
                "rank_show": [1, 1, 1],
                "fixed_gift": {
                    "1000": {"gold": 3000},
                    "5000": {"gold": 8000, "coin": 200},
                },
            },
            # 活動中心 → 福利基金.  time[key] = [buy days, claim days,
            # grace days] measured from attrs.fund_add_time; return =
            # [minimum deposit, rate, daily cap].  Claim payout is
            # min(money * 10 * rate, cap), once per day.
            "fund": {
                "time": {"1": [0, 7, 7]},
                "return": [100, 0.1, 10000],
            },
            # 活動中心 → 轉盤.  random_gift["6"] is the visible pool: each
            # entry is [ {rewardType: amount} ]; the server grants a random
            # entry per spin.  fixed_gift keys are spin-count milestones.
            "roulette": {
                "start_time": datetime.datetime.utcnow()
                - datetime.timedelta(days=1),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=60),
                "start_lv": 1,
                "coin": 100,
                "fixed_gift": {
                    "10": {"gold": 1000},
                    "20": {"coin": 100},
                    "30": {"gold": 3000},
                },
                "random_gift": {"6": [
                    [{"gold": 500}],
                    [{"gold": 1000}],
                    [{"coin": 20}],
                    [{"mark": 10}],
                    [{"avatar_soul": {"A_1001_2": 1}}],
                    [{"equip_soul": {"E_1001_1": 1}}],
                    [{"gold": 2000}],
                    [{"culture_book": 5}],
                ]},
            },
            # 活動中心 → 排行榜.  rank_sort ids are returned by
            # user.get_newzone_ranks and named by language id 20385
            # ("name1$name2$name3").
            "rank": {
                "rank_end": 30,
                # PanelHelpAvatar.countTypeScore(): [hero by star-1,
                # other avatars by star-1, multiplier when owned].
                "pic_coin": [[100, 200, 300, 400, 500, 600],
                             [50, 100, 150, 200, 250, 300], 2],
                # rank_sort ids double as keys into gift; ItemActivityRank
                # reads gift[id]["1"] and gift[id]["2"] for its two reward
                # slots, so both must exist or the list renderer #1010s.
                "gift": {
                    "rank_sort": [1, 2, 3],
                    "1": {"1": {"gold": 2000}, "2": {"gold": 800}},
                    "2": {"1": {"coin": 100}, "2": {"gold": 1500}},
                    "3": {"1": {"mark": 100}, "2": {"gold": 1000}},
                },
                "rank_help": {"1": 20397, "2": 20397, "3": 20397},
            },
            # 遠征: open_time is indexed by weekday; 0 means open.
            # >0 means the weekday is open (checkOpen_expedition tests
            # `open_time[day] <= 0` and inverts it).
            "expedition": {"open_time": [1, 1, 1, 1, 1, 1, 1],
                           "start_lv": [1, 0]},
            # VIP 祭坛 tab (PanelCasinoVIP -> user.get_lottery_activity).
            # Fixed dates keep attrs.lottery_activity.start_time stable across
            # server restarts (the client resets its score when it changes).
            "extract_avatar": {
                "start_time": datetime.datetime(2026, 1, 1),
                "start_vip_level": 0,
                "end_time": datetime.datetime(2035, 1, 1),
                # PanelCasinoVIP reads coin_one/coin_ten directly.
                # 2026-10-22: no ten-draw discount (300 x 10).
                "coin_one": 300, "coin_ten": 3000,
                # Activity points gained per draw; spent in 積分兌換.
                "score_one": 10, "score_ten": 100,
                # 2026-10-24 UP rotation info for the VIP altar timer.
                "up_family": _UP_FAMILY,
                "up_end_time": _UP_END,
                # PanelInteGralExchange: [[gift, need_score], ...].
                "exchange": _altar_exchange_cfg(),
            },
            "sign_in": {
                "0": {"num": 7, "mcid": "A_1078_",
                      "reward": {"gold": 1500, "coin": 100}},
                "1": {"num": 7, "mcid": "A_1078_",
                      "reward": {"gold": 3000, "coin": 150}},
                "2": {"num": 7, "mcid": "A_1078_",
                      "reward": {"gold": 5000, "coin": 200}},
                "3": {"num": 7, "mcid": "A_1078_",
                      "reward": {"gold": 8000, "coin": 300}},
            },
        },
        # 祭坛 info ticker (PanelCenterShopVIP.infoUIsA/B/C reads these
        # unconditionally).  Start times must be Dates; info entries are
        # plain CJK strings, empty lists are fine.
        "ploy_cycle": {
            "start_time": datetime.datetime.utcnow(),
            "cycle_days": 7,
            "info": ["金幣祭壇：消耗金幣或積分，抽新手英雄；點券祭壇：消耗點券，抽進階英雄。"],
        },
        "wager_festival": {"coin": [], "score": []},
        "exchange": {
            # PanelExchange: avatar rows are id -> medal cost.  ItemExchange
            # slices the id on "_" (type_0000_star) and opens the hero detail.
            "avatar": {
                "start_time": datetime.datetime(2026, 1, 1),
                "cycle_days": 7,
                "cycle_exchange": _medal_cycle_cfg(),
                "exchange": _medal_avatar_exchange_cfg(),
            },
            # Equip rows are id -> [medal, vip_level]; all equipment is
            # delisted (user rule 2026-10-22).
            "equip": {
                "info": "裝備兌換已下架。",
                "exchange": _medal_equip_exchange_cfg(),
            },
        },
        # 羈絆 / 陣位 (PanelCenterDNTeam.getDestinyMyAll).  Entry format:
        #   [bond-name language id, [condition ids], [stat, value, mode]]
        # mode 0 = percentage bonus, mode 1 = flat bonus.  Equipment
        # conditions match the hero's equipped eid prefix; avatar
        # conditions match teammates with the same family.
        "destiny": {
            "A_1137": [
                [90823, ["E_1032_6"], ["ap", 2.0, 0]],
                [90824, ["E_3009_6"], ["hit", 1.0, 0]],
                # 2026-10-23 user: bond 3 grants +50% crit rate.
                [90825, ["E_5009_6"], ["crit", 500, 1]],
            ],
            # 鋼鐵俠提摩 (A_1310) equipment bonds (2026-10-22).
            # mode 0 = percentage: hit +100%, attack +50%, magic defence +100%.
            "A_1310": [
                [90826, ["E_1001_6"], ["hit", 1.0, 0]],
                [90827, ["E_4023_6"], ["ap", 0.5, 0]],
                # 2026-10-23 user: bond 3 grants +40% crit damage.
                [90828, ["E_5007_6"], ["critdmg", 0.4, 0]],
            ],
            # 聯盟之喙艾尼維亞 (A_1216) equipment bonds (2026-10-22).
            # 原初聖盾 → +50% HP, 冥霜之翼 → +100% dodge,
            # 干擾水晶 → +100% hit.
            "A_1216": [
                [90829, ["E_1501_6"], ["hp", 0.5, 0]],
                [90830, ["E_3007_6"], ["flee", 1.0, 0]],
                [90831, ["E_4004_6"], ["hit", 1.0, 0]],
            ],
            # 費德提克 (A_1079) equipment bonds (2026-10-23 user design).
            "A_1079": [
                [90835, ["E_1030_6"], ["ap", 0.5, 0]],
                [90836, ["E_3010_6"], ["flee", 1.0, 0]],
                [90837, ["E_4003_6"], ["hit", 1.0, 0]],
            ],
            # 伊莉絲 (A_1036) equipment bonds (2026-10-24 user design).
            # 毒晶蛛刃 → +50% 攻擊；幽影蛛袍 → +50% 生命；
            # 絕情毒蕊 → +40% 暴傷。
            "A_1036": [
                [90839, ["E_1012_6"], ["ap", 0.5, 0]],
                [90840, ["E_3005_6"], ["hp", 0.5, 0]],
                [90841, ["E_4018_6"], ["critdmg", 0.4, 0]],
            ],
            # 兔寶寶提莫 (A_1209) equipment bonds.
            # 毒菇吹箭 → +50% 攻擊；致幻菌傘 → +100% 命中；
            # 狡兔戰靴 → +100% 閃避。
            "A_1209": [
                [90842, ["E_1013_6"], ["ap", 0.5, 0]],
                [90843, ["E_4017_6"], ["hit", 1.0, 0]],
                [90844, ["E_5005_6"], ["flee", 1.0, 0]],
            ],
            # 圖奇 (A_1099) equipment bonds.
            # 瘟疫之弩 → +50% 攻擊；疫鼠圖騰 → +40% 暴傷；
            # 潛行鼠靴 → +100% 閃避。
            "A_1099": [
                [90845, ["E_1005_6"], ["ap", 0.5, 0]],
                [90846, ["E_4001_6"], ["critdmg", 0.4, 0]],
                [90847, ["E_5010_6"], ["flee", 1.0, 0]],
            ],
        },
        "exchange_festival": {"avatar": [], "equip": []},
        "bookskill": {},
        # 角色天賦 (PanelAvatarTalentAvatar).  Ids must have five
        # underscore-separated parts: Talent.getImage uses [0..2], the panel
        # uses [2] as the tier and [4] as xx+2.  At least ten entries per
        # tier are required by GlobalFunction.getRandomNumber(10,10).
        "talent": {
            "H_%03d_%d_0_%d" % (i, star, star): {
                "name": name, "name_tw": name,
                "info": info, "info_tw": info,
                "pl": [i % 8, 50 + i * 5, 0],
            }
            for star in range(2, 8)
            for i, (name, info) in enumerate([
                ("攻擊強化", "提升攻擊力"),
                ("生命強化", "提升生命值"),
                ("防禦強化", "提升防禦力"),
                ("暴擊強化", "提升暴擊率"),
                ("抗暴強化", "提升抗暴率"),
                ("命中強化", "提升命中"),
                ("閃避強化", "提升閃避"),
                ("速度強化", "提升速度"),
                ("韌性強化", "提升韌性"),
                ("怒氣強化", "提升初始怒氣"),
            ])
        },
        # 256 equip templates generated from the client's EQ_* icons.
        "equip": _equip_cfg(),
        # Effect-set table (see _effect_table(): ids now point at the
        # DragonBones animations embedded in the SWF's effectDB skeleton).
        "effect": _effect_table(),
        # GlobalFunction.getVipObj() indexes mConfig_vip[vip_lv].
        #   gift           = free level-up gift (PanelCenterTaskAward)
        #   gift_buy       = {pay:[], data:{}} VIP-level claim (ItemVIPShopping
        #                    status 0); pay[0] is display-only
        #   gift_coin_buy  = {pay:[old, now], data:{}} coin purchase
        #                    (ItemVIPShopping status 1)
        # VIP 0-15 (matches the master build's 16-row privileges list).
        # need_exp[lv] is the experience needed for the step lv -> lv+1;
        # GlobalFunction.getVipEXP(lv) sums 1..lv-1, so the client shows the
        # cumulative requirement to reach that level.
        "vip": {
            str(lv): {
                "need_exp": _VIP_STEP_EXP[lv],
                # GlobalFunction.getEquipRiseMaxLv() = player lv + this.
                "equip_lvmax": lv * 10,
                "leadership_up": 1 if lv else 0,
                "avatar_len_add": 5 * lv,
                "friend_len_add": 5 * lv,
                "buy_energy": lv,
                "gift": [{"gold": 500 * lv}] if lv else [],
                "gift_buy": ({"pay": [0],
                              "data": {"gold": 500 * lv,
                                       "coin": 50 * lv}}
                             if lv else {"pay": [0], "data": {}}),
                "gift_coin_buy": ({"pay": [5000, 1000],
                                   "data": {"gold": 2000 * lv}}
                                  if lv else {"pay": [0, 0], "data": {}}),
            }
            for lv in range(16)
        },
        "pay_config": {},
        # PanelCenterMain.getNewStartTime() reads this.  open_status=1 makes
        # the 公會 building appear; the sub-features stay closed (level gates
        # are also enforced client-side) so only the member tab is used.
        "association_simple": {
            # 2026-10-24 user rule: the guild system is blocked entirely;
            # open_status=0 hides the lobby 公會 building and its entry points.
            "open_status": 0,
            "the_guild_info": {
                "guild_name": 7,
                "user_level_limit": 1,
                "join_level_limit": 1,
                "create_gold": 1000,
                "create_coin": 100,
                "create_gold_lv": 1,
                "create_coin_lv": 1,
                "exit_guild_punish": "0",
                "punish_money": 0,
                "change_name_gold": 500,
            },
            # ItemGuildPanel/guild info header index this by guild level.
            "guild_level": {
                "level_1": {"max_member_length": 30, "guild_shop_level": 1,
                            "flourishing": 100},
                "level_2": {"max_member_length": 40, "guild_shop_level": 2,
                            "flourishing": 200},
                "level_3": {"max_member_length": 50, "guild_shop_level": 3,
                            "flourishing": 300},
                "level_4": {"max_member_length": 60, "guild_shop_level": 4,
                            "flourishing": 400},
                "level_5": {"max_member_length": 70, "guild_shop_level": 5,
                            "flourishing": 500},
            },
            # The four guild sub-tabs read need_guild_lv/open_status.  With
            # open_status=0 the client shows its "not open" hint instead of
            # sending requests we have no content for.
            "the_guild_pvp": {
                "open_status": 0,
                "need_guild_lv": 2,
                "need_guild_number": 10,
                "change_team": 100,
                "schedule_interval": 5,
                "war_zone": [],
                "inspire": {"use_coin": [10, 20], "gift": {"guild_currency": 10}},
                "gift": {"season_gift": []},
                "time": {
                    "start_time": datetime.datetime.utcnow(),
                    "cycle": 1440,
                    "guild_sign_up": 0,
                    "match": 0,
                    "member_sign_up": 0,
                    "get_ready": 0,
                    "fight": 0,
                    "interval": 0,
                },
            },
            "guild_BOSS": {
                "open_status": 1, "need_guild_lv": 1,
                "open_times": [[0, 0]], "duration": 1440,
                # 公會首領: coin cost of an extra attack and daily free hits.
                "need_coin": 100, "free_num": 5, "vip_free_num": 5,
                # PanelGuildBossGetDayAward reads gift.kill_gift.{gold,
                # guild_currency, flourishing}.
                "gift": {"kill_gift": {"gold": 1000,
                                       "guild_currency": 50,
                                       "flourishing": 10}},
            },
            "guild_shop": {
                "open_status": 1, "need_guild_lv": 1,
                # 神秘商店 (sever_shop) only; the 荣耀 shop stays closed so
                # isSever=0 and the client shows a single radio tab.
                "sever_shop": {
                    "open": True,
                    "refresh_interval": 24,
                    # [first refresh cost, per-refresh increment]
                    "hand_renovate": [10, 10],
                    # gift_info[slot][index] = [ [reward, pay, need_lv], 0 ];
                    # the client pushes its own index object onto this array
                    # and then reads element [2], so it must have length 2
                    # before the push.
                    "gift_info": {
                        "0": [[[{"gold": 1000},
                               {"guild_currency": 20}, 1], 0]],
                        "1": [[[{"avatar_soul": {"A_1001_2": 5}},
                               {"guild_currency": 30}, 1], 0]],
                        "2": [[[{"equip_soul": {"E_1001_1": 5}},
                               {"guild_currency": 30}, 1], 0]],
                    },
                },
                "guild_shop": {"open": False, "gift_info": {}},
            },
            # 公會研究 (PanelGuildBase tab 4).  exchange_cost_info entries
            # with type 0 are the 普通 trade rows (paid in gold), type 1 the
            # 高級 rows (paid in coin).  exchange_count_info caps daily
            # exchanges per VIP level.
            "guild_contribute_info": {
                "open_status": 1, "need_guild_lv": 1,
                "exchange_cost_info": {
                    "1": {"cost": 500, "contribute": 10, "type": 0},
                    "2": {"cost": 1500, "contribute": 35, "type": 0},
                    "5": {"cost": 500, "contribute": 15, "type": 1},
                    "6": {"cost": 2000, "contribute": 75, "type": 1},
                },
                "exchange_count_info": {
                    str(v): {"normal": 5, "expert": 3} for v in range(6)
                },
            },
            "guild_graduate": {
                # level is indexed by the target skill level; [0] is unused.
                "guild_graduate_skill": {
                    str(i): {
                        "name": name, "name_cn": name,
                        "description": desc, "description_cn": desc,
                        "icon": i,
                        "level": [None] + [
                            {"up_demand": 50 * lv, "value": 3 * lv}
                            for lv in range(1, 11)
                        ],
                    }
                    for i, (name, desc) in enumerate([
                        ("攻擊強化", "提升全體攻擊"),
                        ("生命強化", "提升全體生命"),
                        ("防禦強化", "提升全體防禦"),
                        ("暴擊強化", "提升全體暴擊"),
                    ])
                },
                "vip_use_skill_count": {str(v): 1 + v for v in range(6)},
                "guild_use_skill_count": {str(v): 2 + v for v in range(1, 11)},
                "change_skill_cost": {str(lv): 200 * lv for lv in range(1, 11)},
            },
            # 公會祈福: each row = [cost, guild flourishing gain, display].
            # type 0 is paid in gold, types 1/2 in coin.
            "guild_worship": [
                [1000, 10, "1000"],
                [50, 20, "50"],
                [100, 40, "100"],
            ],
            "guild_worship_times": 3,
            # 成員祈福 (guild currency pool) — same three tiers.
            "member_worship": [
                [20, 5, "20"],
                [50, 12, "50"],
                [100, 30, "100"],
            ],
            "member_worship_times": 3,
            "a_key_message": {},
        },
        # PanelCenterPVE.addList_h() unconditionally does list[0].id, so the
        # normal PVE tab needs at least one chapter; "combat" is the number of
        # stages in the chapter (also used by ItemPVEmain.delayShowAvatars).
        # NB: chapter ids deliberately avoid M_001/M_002.  ItemPVEcombat
        # hardcodes guide triggers on the exact ids "M_001_3" (guide M1_1)
        # and "M_002_1" (guide M1_3); instantiating those cards starts a
        # scripted guide we have no data for, which crashes the panel.
        # indexID_s is sorted DESCENDING, so chapter 1 gets the largest value
        # and the newest unlocked chapter is auto-selected.  20 chapters x 4
        # stages; the maps live in _combat_main().
        "battle_main": _battle_main_cfg(),
        "battle_association": {},
        "combat_association": {},
        # UI strings normally come from GlobalLanguageStr: it first looks in
        # cfg.return_msg_config ($mConfig_msg).  The client SWF only ships a
        # tiny partial language xml, so put debug-visible text for the codes
        # we care about here.
        "return_msg_config": {
            # The client SWF only ships a tiny partial language xml, so these
            # ids would otherwise render as an empty dialog.  Values must be
            # CJK: the embedded Csjcyy font has no ASCII glyphs.
            "31000": "操作有誤", "31001": "操作有誤",
            "20121": "確定", "20018": "隊伍", "20041": "隨機",
            "20042": "出戰",
            # PanelGameEndAward's three bottom buttons
            "20464": "再次挑戰", "20295": "下一關", "20465": "返回",
            "20021": "確定", "20104": "取消",
            "90097": "勝利", "90098": "失敗", "90035": "戰鬥結算",
            # PanelDetailAll action buttons
            "20085": "吞噬升級", "20092": "升星",
            "90553": "培養", "25025": "編隊",
            "20091": "英雄技", "25021": "準備：@0  冷卻：@1", "31020": "無",
            # UiLayer.addInfo() busy-waits for a non-empty string in the
            # 46100..46199 tips range; with none the whole game freezes
            # in an infinite loop after the battle.
            "46100": "點擊屏幕繼續",
            # Task descriptions (PanelCenterTaskAward task.info)
            "91001": "累計登錄", "91002": "主線通關", "91003": "等級提升",
            # PanelActivitySign labels / popups.  getLanguageStr() formats
            # with @0, @1 placeholders.
            "90532": "簽到", "90539": "領取獎勵",
            "90536": "還需@0天", "90540": "獎勵已可領取",
            "90542": "點擊植物即可簽到", "90543": "今日已簽到",
            "90544": "請先領取獎勵", "90538": "簽到成功",
            "90131": "獲得獎勵", "90140": "簽到功能未開啟",
            # 探險 map/team panel labels.
            "90595": "請先完成當前關卡", "10030": "請先完成前面的關卡",
            "90597": "刷新", "90606": "戰鬥",
            "90608": "當前增益：@0", "90656": "消耗",
            "90598": "免費刷新次數@0", "90607": "請選擇出戰英雄",
            "90660": "第@0關", "90279": "戰力：",
            "90599": "花費@0刷新？", "90554": "確定",
            "20363": "攻擊次數@0  傷害@1", "20368": "傷害加成",
            "20369": "距離復活@0秒", "20370": "等待復活@0秒",
            "20372": "超級復活傷害+@0%", "20356": "獎勵",
            "90136": "花費@0點券復活？", "90137": "花費@0點券復活並提升@1%傷害？",
            "90141": "獎勵已領取",
            # PVP bracket names + map name.
            "92001": "青銅競技場", "92002": "白銀競技場",
            "92003": "黃金競技場", "92004": "鉑金競技場",
            "92005": "鑽石競技場", "92006": "王者競技場",
            "92010": "王者峽谷",
            # 德諾之陣 node names / labels.
            "25034": "需要等級@0", "25035": "需要魂石@0",
            "25038": "當前@0", "25039": "下一級@0",
            "25040": "消耗魂石@0", "25045": "尚無陣位",
            "25053": "屬性",
            "25046": "生命之陣", "25047": "生命之陣貳",
            "25048": "攻擊之陣", "25049": "攻擊之陣貳",
            "25050": "物防之陣", "25051": "物防之陣貳",
            "25052": "法防之陣", "25060": "法防之陣貳",
            "25054": "命中之陣", "25055": "閃避之陣",
            "25056": "暴擊之陣", "25057": "堅韌之陣",
            "25058": "全能之陣",
            # ItemDNavatar passes (unlockLv, unlockStone): @0 is the level,
            # @1 the stone cost.
            "90425": "花費@1魂石開啟陣位（需等級@0）",
            "90428": "等級不足，需要@0級",
            "90429": "魂石不足，需要@0",
            "90430": "消耗@0魂石升級陣位？",
            "90431": "魂石不足，需要@0",
            "90513": "已達最高等級@0",
            "10127": "選擇角色", "90452": "德諾之陣",
            "25028": "生命", "25029": "攻擊", "25030": "物防",
            "25031": "法防", "25033": "魂石", "25041": "選擇角色",
            # 祭壇 labels.
            "20059": "金幣祭壇", "20068": "點券祭壇",
            "97926": "VIP祭壇", "97982": "VIP@0解鎖",
            "90383": "勳章兌換", "97680": "積分兌換",
            "90382": "祭壇說明",
            "97941": "金幣祭壇抽新手英雄；點券祭壇抽進階英雄；VIP祭壇有保底。",
            # 競技場.
            "20289": "挑戰", "20290": "復仇", "20291": "挑戰",
            "20303": "排行", "20304": "訊息", "20361": "機器人",
            "20362": "不可挑戰", "90657": "競技次數", "97061": "賽事規則",
            "25054": "命中之陣",
            # 商城 / VIP 兑换页.
            "20095": "體力", "20096": "英雄", "20097": "好友", "20098": "競技",
            "20146": "購買", "90488": "VIP禮包", "90378": "禮包內容",
            "90379": "可購買", "20322": "原價@0", "97600": "豪華禮包",
            "97601": "提示", "97602": "現價", "97603": "花費@0購買VIP@1禮包？",
            "90120": "VIP等級不足@0", "97606": "已達最高VIP等級@0",
            "90062": "獲得@0",
            # 商城 → 商店 purchases.
            # PVE stamina purchase confirm (ItemPVEcombat / ItemShop /
            # popEnergy).  The purchase refills stamina to the current cap,
            # so state the currency and that it is a full refill.
            "90002": "花費@0點券回復全部體力？剩餘購買次數@2次",
            "90003": "體力已滿",
            "90004": "花費@1將英雄容量擴充@0格？目前@2，上限@3",
            "90005": "英雄容量已達上限",
            "90006": "花費@1將好友容量擴充@0格？目前@2，上限@3",
            "90007": "好友容量已達上限",
            # 活動中心 → 排行榜.
            "20385": "等級排行$戰鬥力排行$競技排行",
            "20386": "時間：@0", "20392": "查看",
            "20393": "金幣：@0", "20397": "排行榜說明",
            "90138": "暫無排行資料",
            "20387": "未開始", "20395": "已結束", "20396": "進行中",
            "25026": "第1名獎勵", "25027": "第2名獎勵",
            # 活動中心 → 轉盤.
            "20503": "每次消耗", "90510": "今日免費",
            "20422": "抽一次", "20423": "抽十次",
            "20426": "已抽@0次", "20424": "第@0次",
            "20427": "抽@0次需要@1點券？",
            "97629": "恭喜@0獲得@1",
            # 公會首領 labels.
            "97906": "攻擊", "97890": "剩餘次數@0", "97891": "已擊殺@0",
            "97858": "傷害排行", "97764": "獎勵預覽", "97841": "花費@0",
            "97917": "購買攻擊次數", "97893": "我的排名@0",
            "97908": "擊殺獎勵", "97059": "剩餘時間@0", "97060": "已結束",
            "20485": "已結束", "97852": "公會商店說明",
            "97909": "公會首領說明",
            "10075": "購買次數已達上限",
            # 戰敗翻牌.
            "90460": "戰鬥獎勵", "90461": "恭喜獲得",
            # 碎片名稱（Fragment.getFragName 會用 31008 拼裝）.
            "31008": "@0碎片@1", "31009": "@1星@0碎片",
            "31010": "一", "31011": "二", "31012": "三",
            "31013": "四", "31014": "五", "31015": "六",
            # 神秘商店 / 英雄戰魂 / 裝備戰魂 (PanelCenterSoul).
            "90578": "神秘商店", "90579": "普通", "90580": "高級",
            "90581": "超級", "90582": "將在@0後刷新",
            "90583": "售價", "90584": "刷新需要@0點券",
            "90587": "購買成功", "90588": "花費@0點券刷新@1？",
            "90592": "花費@0@1購買@2@3（@4/@5）",
            "90646": "已購買", "90647": "刷新", "90653": "花費@0@1購買@2@3",
            "90654": "花費@0@1購買@2@3",
            "97506": "英雄戰魂", "97507": "裝備戰魂",
            "97508": "已擁有@0/@1", "97509": "魂石",
            "97511": "需要@0魂石", "97512": "尚未收集英雄戰魂",
            "97513": "尚未收集裝備戰魂", "97514": "獲得@0",
            "97515": "獲得@0", "97516": "需要@0裝備戰魂",
            # 公會商店.
            "97856": "神秘商店", "97857": "榮耀商店",
            "97855": "公會幣", "97854": "每日刷新",
            "97918": "花費@0公會幣刷新？", "97920": "公會幣不足",
            "97921": "公會幣不足", "97929": "剩餘@0",
            "97930": "剩餘@0", "97931": "需要公會等級@0",
            "97932": "公會等級@0", "97942": "公會等級不足",
            "97517": "商店說明",
            "97518": "普通神秘商店，出售英雄與裝備。",
            "97519": "高級神秘商店，貨品更為稀有。",
            "97520": "超級神秘商店，可購得頂級英雄與裝備。",
            "20432": "兌換", "90600": "還需@0魂石",
            "90604": "已可兌換@0",
            "20149": "點券", "20162": "金幣", "20317": "x@0",
            "31006": "等", "20505": "沒有可選裝備",
            # 軍營 (PanelSocialMainAvatar) tabs, filters and footer.
            "70003": "查看", "20072": "出售",
            "20236": "全部", "20165": "英雄", "20255": "小怪",
            "20256": "建築", "20257": "材料",
            "20205": "@0星@1", "20193": "x",
            "90115": "請選擇足夠的材料",
            "90128": "請放入升星材料", "90019": "升星材料不足",
            "10165": "該角色無法升星", "90018": "英雄等級未滿，無法升星",
            "90020": "確定要升星嗎？", "90024": "統御力不足，無法升星",
            # 培養 panel.
            "90572": "培養", "90568": "培養方式", "90569": "選擇消耗",
            "90570": "培養上限", "90655": "請先選擇培養方式",
            "90645": "此功能暫未開放",
            # 2026-10-25: the pith shown on the hero detail comes from 升階
            # (phase_up +30 per phase), not the closed 培養 feature; label it
            # 潛能 so the value no longer contradicts the locked 培養 button.
            "20226": "潛能屬性",
            "90521": "生命@0（+@1）　攻擊@2（+@3）\n物防@4（+@5）　法防@6（+@7）\n潛能值@8/@9",
            "90575": "培養材料不足", "90081": "點券不足",
            "10183": "請先完成當前培養",
            "20271": "保存", "20270": "取消",
            # 裝備面板 tabs, filters and action labels.
            "20259": "鍛造", "20260": "洗煉", "20406": "參悟",
            "20462": "附魔", "90191": "拆解", "20006": "裝備",
            # Slot order is 2 weapons, armor, accessory, boots, skill book.
            # E_4 is the accessory slot (not a helmet) and E_6 is the skill
            # book slot (checkEquipIsBook() returns true for every E_6 id).
            "20263": "武器", "20264": "護甲", "20265": "飾品",
            "20266": "靴子", "20267": "技能書",
            "20407": "參悟", "20408": "參悟進度@0",
            "90108": "光環屬性提升@0%",
            "90080": "標記不足", "90082": "洗煉失敗",
            "90113": "次數不足", "90671": "點券",
            "20272": "金幣", "20273": "潛能",
            # PanelEquipWash builds these labels without an argument; @0
            # would stay visible.  The 10x option is its own literal.
            "90563": "洗煉", "90564": "洗煉十次",
            "20313": "洗煉屬性", "20320": "光環@0級 +@1%",
            # 20321 is the unused potential shown in the wash/alchemy panel.
            # 30021..30024 are the four secondary stats (匹配客户端内置
            # language_tw_xml): 命中/閃避/暴擊/韌性.  They were mistakenly
            # set to 生命/攻擊/物防/法防, which are 20283..20286.
            "20321": "潛能：", "30021": "命中：", "30022": "閃避：",
            "30023": "暴擊率：", "30024": "暴擊抵抗：", "30026": "暴傷：",
            # 附魔粉塵：LOL_MagicButton.TXT_STR 按下標讀 90193..90196，
            # 90197 是 "@n$@n$..." 形式的四色名稱串（供提示文字拆分）。
            "90193": "綠色粉塵", "90194": "藍色粉塵",
            "90195": "紫色粉塵", "90196": "橙色粉塵",
            "90197": "綠色粉塵$藍色粉塵$紫色粉塵$橙色粉塵$光之粉塵",
            # TXT_SYMP：附魔成功提示裡的屬性/顏色名稱。
            "31021": "綠色", "31022": "藍色",
            "31023": "紫色", "31024": "橙色",
            "90202": "花費@0@1附魔@2？", "90199": "需要@0@1進行附魔",
            "90203": "附魔說明", "20283": "生命：", "20284": "攻擊：",
            "20285": "物防：", "20286": "法防：",
            "90201": "獲得@0附魔", "90205": "附魔@0",
            "90010": "提示", "97004": "請選擇材料",
            "90703": "煉化+@0", "20079": "等級：@0", "20268": "選擇",
            "90162": "已達最高等級", "10061": "請先保存或取消當前操作",
            "10023": "金幣不足", "20287": "射程：", "20288": "速度：",
            "20477": "祭壇", "20093": "商店", "20315": "兌換",
            "20186": "VIP", "20504": "VIP特權",
            # Altar draw-card titles (PanelCasinoA/B/VIP): left single,
            # right ten.  Kept separate from 20063/20064, which still label
            # the three altars on the hub.  90760/90761 are already used by
            # the guild research panel, so use the free 90810/90811 slots.
            "90810": "單抽", "90811": "十連抽",
            "90812": "已達最高星級",
            # Hero lock button and team-member ribbons.
            "90819": "上鎖", "90820": "解鎖",
            "90821": "隊長", "90822": "隊員",
            # 莫德凱撒 equipment bonds (destiny config).
            "90823": "鐵獄契約", "90824": "鋼鐵之軀", "90825": "寂途同行",
            # 鋼鐵俠提摩 equipment bonds.
            "90826": "所向無敵", "90827": "我心如鐵", "90828": "堅不可摧",
            # 聯盟之喙艾尼維亞 equipment bonds (2026-10-22).
            "90829": "凜冬之盾", "90830": "凜冬之翼", "90831": "凜冬之眼",
            # Same-hero team restriction (2026-10-23).
            "90832": "同一隊伍不能上陣重複英雄",
            "90834": "鍛造滿級後才能洗煉",
            "90835": "收割恐懼", "90836": "吞噬希望",
            "90837": "洞穿虛妄",
            "90838": "技能詳情",
            # 伊莉絲/兔寶寶提莫/圖奇 equipment bonds (2026-10-24).
            "90839": "毒牙淬鍊", "90840": "蛛影護體", "90841": "絕情蝕心",
            "90842": "菇毒淬箭", "90843": "幻菌致毒", "90844": "狡兔三窟",
            "90845": "疫毒連弩", "90846": "鼠疫圖騰", "90847": "暗巷疾行",
            # 2026-10-24: 吞噬升級「一鍵」按鈕（自動選取全部小怪）。
            "90848": "一鍵",
            # VIP altar 48h UP rotation countdown.
            "90849": "UP輪換倒數：", "90850": "輪換中",
            # Equipment forge: level-gated cap (distinct from 90084 max level).
            "90851": "請先提升召喚師等級",
            # Passive book skill label (LOL_DetailEquip.skill).
            "90833": "被動",
            "20192": "詳情", "90420": "VIP特權",
            "90458": "當前VIP經驗@0", "20506": "升級需要@0經驗",
            # Shared "feature closed" hint (PVP/guild locked tabs).  At max
            # VIP level ItemVIP also shows it, where it reads as "capped".
            "90046": "暫未開放",
            "20458": "拆解", "90079": "拆解@0可獲得@1金幣與@2",
            "90682": "第@0月簽到", "90683": "第@0天",
            "90684": "規則", "90685": "VIP等級不足",
            "90686": "今日已領取", "90687": "VIP@0雙倍",
            # 探險 labels.
            "90549": "進入探險", "90550": "選擇出戰英雄",
            "90552": "已選@0/@1", "90554": "確定", "90573": "至少選擇3名英雄",
            "90560": "刷新次數@0", "90566": "第@0關",
            "20401": "戰力@0/@1", "20170": "@0", "90649": "探險說明",
            "20356": "獎勵", "20357": "上期", "20358": "首領開放時間",
            "20359": "已結束", "20360": "距離開啟@0",
            # 遠征.
            # 2026-10-23: 遠征 = 分解；英雄會被消耗。
            "90190": "選擇英雄派遣遠征（分解），英雄將被消耗，可獲得魂石、積分與獎勵。",
            "90210": "確定派遣英雄遠征？遠征的英雄將被消耗，無法返還。",
            "90209": "請選擇英雄",
            "98054": "該英雄正在其他玩法中",
            "90192": "已選擇@0個裝備（上限@1）",
            "20463": "背包@0/@1", "97003": "請選擇要拆解的裝備",
            "20069": "出售角色",
            "90008": "出售@1個角色可獲得@0金幣，確定？",
            "20073": "出售可獲得@0金幣",
            "20074": "已選擇@0個角色（上限@1）",
            "20075": "背包@0/@1",
            "20071": "清空", "20228": "全選",
            # 公會 (guild) main panel.
            "97665": "公會資訊", "97667": "公會戰", "97853": "公會首領",
            "97666": "公會商店", "90749": "公會研究",
            "97677": "公會列表", "97673": "建立公會", "97678": "查找公會",
            "97668": "公會名稱", "97669": "名稱最多@0個字",
            "97670": "公會徽章", "97672": "建立消耗",
            "97714": "金幣建立", "97715": "鑽石建立",
            "97716": "鑽石", "97674": "查找", "97675": "公會ID",
            "97676": "查找", "97785": "請輸入5位公會ID",
            "97763": "目前沒有公會，快來建立或加入一個吧！",
            "97724": "公會ID：@0", "97723": "成員 @0/@1",
            "97728": "公會日誌", "97727": "成員管理",
            "97725": "公會活躍", "97726": "其他",
            "97729": "公會公告：@0", "97732": "退出公會",
            "97733": "膜拜", "97719": "建立公會失敗",
            "97848": "請輸入公會名稱", "97860": "功能暫未開放",
            "97933": "金幣建立需要等級@0", "97934": "鑽石建立需要等級@0",
            "20514": "Lv.@0", "97082": "會長", "97083": "副會長",
            "97084": "成員",
            # PanelGuildManager (公會管理) buttons/messages.
            "97686": "公會管理", "97687": "申請審核",
            "97688": "成員管理", "97689": "修改公告",
            "97690": "公會設置", "97691": "發布資訊",
            "97692": "解散公會", "97679": "花費@0@1建立公會？",
            "97819": "權限不足", "97835": "操作失敗",
            "97745": "操作成功", "97754": "公會",
            "97786": "公會名稱重複",
            # ---------------------------------------------------------------
            # Restored activity / guild / alchemy / talent / shop labels.
            # Keeping them server-side avoids blanks in the stripped client
            # language XML.  Placeholders follow GlobalLanguageStr's @N.
            # 活動中心 → 充值返利（基金）
            "20185": "認購", "20444": "領取",
            "20446": "活動時間：@0", "20447": "可領取@0點券",
            "20449": "領取截止：@0", "20499": "返利@0", "20500": "點券",
            "90167": "存入@0點券，每日返還@1%，每日上限@2",
            "90168": "獲得返利@0點券", "90170": "今日已領取",
            "90490": "活動剩餘", "90498": "本金@0",
            # 活動中心 → 競猜
            "20402": "競猜", "20502": "點券",
            "90143": "競猜玩法：消耗點券報名，獲勝可獲得雙倍返還",
            "90144": "活動已結束", "90146": "競猜",
            "90147": "活動尚未開始", "90148": "快來參與競猜吧",
            "90150": "活動已結束", "90151": "截止時間：@0",
            "90491": "活動剩餘：@0",
            "90504": "每次競猜費用會遞增，請注意點券餘額",
            "90505": "活動結束",
            # 活動中心 → 團購
            "20469": "排行榜", "20511": "累計消費", "20512": "累計返還",
            "90212": "已達@0份", "90259": "獎勵", "97053": "已結束",
            "97056": "份", "97058": "團購進度",
            "97633": "全服已購@0份", "97634": "我的購買@0份",
            "97645": "購買", "97649": "與全服玩家一起團購，達成目標領取獎勵",
            "97047": "團購獎勵", "97048": "目標@0份", "97646": "獎勵一覽",
            "90135": "排行", "96556": "排名", "97069": "購買份數",
            "97644": "第@0名", "20203": "VIP@0",
            "20394": "售價@0", "90051": "需要@0點券",
            "90493": "花費", "90494": "當前點券",
            "97045": "單買", "97046": "十連", "97049": "團購",
            "97051": "再買一次", "97052": "繼續購買",
            "97639": "購買成功，獲得：",
            "97653": "團購說明：購買禮包可累計全服進度，達成目標領取額外獎勵。",
            "96554": "購買@0份", "97068": "消費@0點券",
            "97062": "已達成@0份", "97067": "獎勵已解鎖",
            # 活動中心 → 轉盤 / 消費排行
            "20173": "領取", "90492": "抽獎",
            "20470": "累計消費：@0", "20471": "第@0名",
            "20476": "活動已結束", "20486": "未上榜", "20501": "消費",
            "90273": "活動時間：@0", "90274": "累計消費@0解鎖",
            "90278": "消費不足", "90336": "消費排行",
            "90277": "排行獎勵", "20472": "未上榜", "90289": "排名獎勵",
            # 活動中心 → 福利
            "20377": "已領取", "90463": "福利",
            "90464": "活動剩餘：@0", "90467": "福利說明",
            "90478": "綠色粉塵", "90479": "藍色粉塵",
            "90480": "紫色粉塵", "90481": "橙色粉塵",
            "90482": "領取剩餘：@0", "90483": "恭喜",
            "90484": "獲得福利，請選擇獎勵",
            "90547": "花費@0@1購買@2@3？",
            "97014": "點券不足", "97015": "金幣不足",
            "97016": "已售罄", "97017": "不可購買",
            "97087": "免費", "97702": "兌換獎勵",
            "97814": "消耗@0@1可獲得@2@3，十連消耗@4@5可獲得@6@7",
            "97815": "火$水$風$雷$光",
            "90468": "福利詳情", "90469": "x@0",
            "90470": "粉塵", "90471": "自動停止@0", "90472": "開始",
            # 煉化 / 天賦
            "90129": "等級不足，需要@0級", "90691": "煉化",
            "98006": "天賦", "98007": "天賦",
            "10503": "天賦點不足", "10504": "天賦操作進行中",
            "98041": "天賦效果",
            "98043": "替換後天賦等級會降低，確定？",
            "98045": "研究", "98046": "當前天賦：",
            "98047": "請先選擇天賦", "98048": "天賦已更新",
            "98049": "天賦已刷新", "90596": "請選擇角色",
            "98050": "天賦選擇", "90702": "煉化說明",
            "90692": "煉化", "90693": "請選擇裝備", "90694": "請選擇裝備",
            "90695": "請選擇材料", "90696": "請選擇裝備",
            "90697": "材料不足", "90698": "確定煉化？",
            "90699": "花費@0@1", "90700": "煉化失敗", "90701": "煉化成功",
            "90705": "暫無可選材料", "90706": "材料",
            "20017": "等級@0",
            "97628": "裝備已有附加屬性，煉化將清空這些屬性，確定？",
            # 公會研究
            "90748": "花費@0@1獲得@2貢獻", "90750": "剩餘次數@0/@1",
            "90751": "已研究", "90752": "研究規則", "90753": "研究技能",
            "90754": "貢獻兌換", "90755": "普通兌換", "90756": "高級兌換",
            "90757": "權限不足", "90759": "說明", "90760": "次數已用完",
            "90761": "效果：@0", "90762": "已達上限", "90763": "已研究",
            "90764": "研究成功", "90765": "學習", "90766": "需要@0貢獻",
            "90767": "貢獻不足", "90768": "貢獻不足", "90770": "替換技能",
            "90771": "未解鎖", "90772": "技能升級", "90773": "升級",
            "90774": "花費@0貢獻將@1升至@2級",
            "90775": "已學習技能數@0", "90776": "研究技能",
            "90777": "選擇技能", "90778": "替換", "90779": "花費@0點券",
            "90780": "點券不足", "90781": "已達研究上限",
            "90782": "消耗@0點券", "90786": "技能欄已滿",
            "90787": "請先學習前一級", "90791": "獲得@0貢獻",
            "90793": "學習成功", "90794": "升級成功", "90795": "替換成功",
            "90796": "不可替換", "90797": "技能效果：@0",
            "90799": "研究完成", "90800": "技能已滿級", "90801": "研究失敗",
            "90803": "技能未解鎖", "90804": "需要公會等級@0",
            "90806": "已學習該技能", "90807": "尚未學習技能",
            "90808": "替換後技能等級保留",
            "10603": "操作失敗", "10604": "次數不足", "20459": "兌換",
            # 公會祈福 / 排行 / 日誌
            "97738": "公會幣", "97740": "公會祈福", "97741": "成員祈福",
            "97791": "繁榮度說明", "97792": "公會祈福可增加公會繁榮度",
            "97793": "距離升級還需@0繁榮度", "97795": "當前繁榮度@0",
            "97797": "公會幣說明", "97798": "當前公會幣@0",
            "97801": "今日祈福次數已用完", "97803": "花費@0",
            "97804": "公會等級@0", "97805": "總繁榮度@0",
            "97806": "還需@0繁榮度升級", "97808": "花費@0@1祈福？",
            "97810": "剩餘次數@0/@1", "97849": "增加繁榮度@0",
            "97919": "公會已升級至@0級", "98005": "祈福成功",
            "97826": "查看繁榮度", "97816": "公會日誌",
            "97744": "全服第@0名", "97844": "本區第@0名",
            "97845": "本區排行", "97846": "全服排行", "97847": "公會排行",
            "97703": "活躍@0", "97742": "成員@0",
            # 商城 / 點券商店
            "20094": "點券", "20224": "點券商店",
            # 2026-10-22 VIP privileges panel texts (these ids are only used
            # by the VIP panels; the previous strings came from the blanket
            # placeholder table and read as shop labels).
            "20184": "祭壇", "20190": "VIP有效期：@0", "20200": "VIP已過期",
            "20201": "VIP經驗加成@0倍", "20318": "VIP特權",
            "20319": "VIP經驗加成",
            "20491": "剩餘", "90116": "剩餘@0", "90117": "元",
            "90380": "購買", "90436": "禮包", "90441": "剩餘",
            "97971": "點券商店", "90149": "金幣", "90387": "剩餘",
            "90489": "購買", "90514": "售罄",
            "95016": "刷新", "95017": "刷新",
            "97960": "點券商店說明", "97961": "使用點券購買稀有道具",
            "90032": "購買次數已達上限", "90068": "購買次數已達上限",
            # 公會資訊 / 加入 / 退出
            "97862": "公會不存在", "97993": "今日已申請",
            "97992": "申請已提交", "97833": "公會已滿",
            "97834": "等級不足", "97830": "申請加入@0？",
            "90758": "貢獻", "97912": "公會戰進行中",
            "97913": "成員報名中", "97914": "下次公會戰：第@0輪",
            "97915": "等待下一輪公會戰", "97773": "賽程",
            "97774": "報名", "97851": "商店規則",
            "97838": "修改公告", "97850": "公會說明",
            "97927": "暫無公告", "97964": "公會等級不足",
            "97718": "公會幣不足", "97861": "已達人數上限",
            "90123": "職位不足", "97706": "不能加入自己的公會",
            # 20005 is shared by team leadership (統御力 x/y), guild member
            # counts (15/36) and foster progress; the surrounding UI already
            # supplies the label, so it must stay bare numbers.
            "97705": "已在公會中", "20005": "@0/@1",
            "20160": "公告：@0", "97704": "需要等級@0",
            "97712": "加入公會", "97709": "申請加入",
            "97710": "取消申請", "97711": "退出公會",
            "97708": "會長不能退出", "97720": "公會不存在",
            "97782": "申請已取消", "97959": "今日申請次數已滿",
            "97863": "公會名稱太長", "98004": "公會名稱包含非法字元",
            "97713": "職位不足", "97864": "退出冷卻中",
            "97832": "退出公會懲罰剩餘@0分鐘",
            # 競技場 (PanelCenterPVP)
            # PanelCenterPVP tab order: 碎片(晶片) / 競技場 / 極限 / 排位賽
            "20347": "碎片", "20277": "競技場", "20278": "極限",
            "96557": "排位賽", "98053": "活動未開啟",
            "90369": "戰鬥資訊", "90443": "印記",
            "20213": "今日次數已用完", "90182": "競技場說明",
            "90351": "賽季剩餘：", "90376": "截止@0",
            "90352": "本賽季已結束", "90353": "新賽季即將開始",
            "90339": "青銅", "90340": "白銀", "90342": "黃金",
            "90343": "鉑金", "90355": "鑽石", "90354": "王者",
            "90533": "排名獎勵", "90335": "競技說明",
            "90252": "規則", "90337": "極限挑戰說明",
            "90253": "賽季時間", "90249": "領取獎勵",
            "90250": "祝福", "90255": "獎勵已領取",
            "90251": "暫無獎勵", "90402": "競技場獎勵",
            "90360": "上賽季結算：@0", "90297": "今日已領取",
            "90303": "排名不足", "90298": "獎勵未發放",
            "90318": "需要等級@0", "90258": "花費@0領取獎勵？",
            "90338": "獎勵已領取", "90299": "剩餘時間@0",
            "90358": "被@0擊敗", "90300": "每日@0:@1-@2:@3",
            "90301": "每日@0:@1-@2:@3", "90302": "每日@0:@1-@2:@3",
            "90312": "發放", "90313": "未發放",
            # 角色詳情 / 吞噬 / 升星
            "20076": "角色詳情", "10182": "該角色無法吞噬",
            "90034": "等級已滿", "90208": "吞噬需要@0金幣？",
            "90053": "吞噬需要@0金幣？", "20090": "統帥：@0",
            "20081": "（滿級@0）", "20024": "生命：@0",
            "20025": "攻擊：@0", "20026": "物防：@0", "20027": "法防：@0",
            "90652": "潛能值@0", "90397": "技能",
            "20492": "技能等級@0", "90021": "暫無技能",
            "90400": "下級經驗@0", "90398": "總經驗@0",
            "90399": "總金幣@0", "90401": "技能點@0",
            "20225": "需要@0@1，好感度@2", "90198": "材料不足",
            "20087": "升星", "98037": "天賦：@0",
            "90368": "升星後", "90022": "技能", "20207": "等級@0",
            "20088": "速度：@0", "20089": "射程：@0",
            "20080": "屬性提升@0%", "20105": "隊長技",
            # 編隊 / 巔峰競技
            "20276": "編隊", "20419": "選擇好友",
            "98011": "巔峰隊伍@0", "20070": "返回",
            "90286": "已報名", "90257": "報名",
            "98010": "開始戰鬥", "98008": "請選擇出戰角色",
            "98042": "隊伍已滿", "98009": "請先選擇角色",
            # PanelDetailAll.up_Triggered uses 10071 when the hero has no
            # further phase/star step (e.g. a 7★ hero clicking 升星).
            "10071": "已達最高星級",
            "20043": "已上陣@0", "31007": "角色已上陣",
            # 戰鬥結算 (PanelGameEndAward)
            "90165": "消耗@0體力再次挑戰？", "20114": "戰鬥勝利",
            "20115": "好友助戰", "20116": "好友助戰",
            "20117": "好友助戰", "20118": "好友助戰",
            "20281": "（進階）", "20108": "戰鬥失敗",
            "90164": "獲得裝備@0", "90163": "背包已滿",
            "20112": "經驗+", "90100": "排名提升至@0",
            "90099": "排名下降", "20111": "金幣", "20297": "經驗",
            "90102": "獲得@0@1", "20312": "競技場",
            "90101": "再次挑戰", "20207": "等級@0", "20229": "（首勝雙倍）",
            "90451": "魂石@0", "90449": "魂石", "90031": "獎勵已領取",
            "32006": "自動戰鬥", "95020": "確定", "97011": "戰鬥獎勵",
            # Level-up popup (PanelFunctionOpenInfo): the title used to read
            # 功能開啟@0 and the leadership row was mislabelled 鑽石.
            "20137": "體力", "97623": "統御力", "97607": "等級提升至@0級",
            # 角色詳情 / 屬性
            # ItemBase.setLvClip() alternates the level text and the phase
            # text in the warehouse tile.  The level line uses 20017="LV.@0"
            # (max level wraps 20180="MAX" -> "LV.MAX").  The client only
            # knows the numeric phase, so the SWF patch in
            # GlobalLanguageStr maps 20292 to 一階/二階/..., and 20314 is the
            # label shown once the hero reaches its maximum phase.
            "20166": "角色|||角色", "20292": "@0階", "20314": "滿階",
            "20034": "命中：@0", "20232": "閃避：@0", "20233": "暴擊率：@0",
            "20234": "暴擊抵抗：@0", "90454": "收起", "20105": "隊長技",
            "20513": "被動技能", "20489": "@0",
            "90455": "上陣", "90456": "下陣", "90675": "無法上陣",
            "90644": "已上陣", "10071": "已達最高星級",
            "20230": "生命成長",
            "20237": "石頭（剋制剪刀，傷害+@0）",
            "20238": "剪刀（剋制布，傷害+@0）",
            "20239": "布（剋制石頭，傷害+@0）",
            "20240": "物理傷害", "20241": "魔法傷害",
            "20242": "真實傷害", "20243": "近戰",
            "20244": "遠程", "20245": "輔助",
            "20235": "其他", "20227": "戰力：@0",
            "90679": "生命：@0（@1）  攻擊：@2（@3）  物防：@4（@5）  法防：@6（@7）",
            # LOL_TeamSet / PanelTeamSet use 20474 for the leadership
            # (統御力) title and 20475 for the team power (戰力) title.
            "20475": "戰力", "10133": "戰力：", "90487": "更換角色",
            # 技能描述 (SkillSet)
            "30100": "@0造成@1傷害", "30101": "@0傷害@1",
            "20468": "準備：@0  冷卻：@1",
            # @0 is filled with GameMapTools.toPercentage(), which already
            # appends "%", so these templates must not contain one.
            # hpType gates the skill on the caster's own HP ratio.
            "24030": "自身生命值高於@0時可用", "24031": "自身生命值低於@0時可用",
            # range classification (LINE_POS = 3000).
            "24011": "超遠程", "24010": "遠程",
            # aoe classification: N extra targets, positional radius,
            # special line-wide sentinel, random targets, self.
            "24003": "直線全體目標（射程@0）", "24000": "攻擊@0個目標",
            "24006": "直線全體目標", "24002": "範圍@0內所有目標",
            "24001": "隨機@0個目標", "24005": "自身", "24004": "單體目標",
            # pl[5] != 0 -> banStand false -> support/healer targets allowed.
            "24020": "可攻擊敵方輔助單位",
            "25000": "眩暈", "25001": "沉默", "25002": "虛弱",
            "25003": "破防", "25004": "中毒（每回合額外造成@0最大生命傷害）",
            "25005": "引燃（每回合持續傷害，治療效果降至@0）", "25017": "詛咒",
            "25006": "召喚", "25007": "護盾", "25008": "強攻",
            "25018": "淨化", "25011": "命中提升", "25012": "閃避提升",
            "25013": "暴擊提升", "25014": "韌性提升",
            "25009": "嘲諷", "25010": "神佑（受到致命傷害時回復@0最大生命）",
            "25019": "鐵壁", "25020": "吸血",
            "20421": "技能：@0 準備@1回合 冷卻@2回合",
            "30003": "Lv",
            # 通用操作 / 提示 (GlobalFunction)
            "32007": "無法使用@0", "10087": "@0不足",
            "20212": "購買", "20195": "VIP特權", "20196": "VIP",
            "20194": "花費@0", "90027": "免費", "20197": "永久",
            "20198": "已全部領取", "70002": "領取", "90507": "操作失敗",
            "90439": "金幣不足", "90440": "點券不足",
            "90011": "背包已滿", "90122": "角色已滿", "10012": "好友已滿",
            "90059": "花費@0金幣？", "90121": "花費@0點券？",
            "20077": "物品已鎖定", "20078": "已鎖定", "20023": "使用",
            "20056": "出售", "20293": "暫無", "20294": "剩餘@0",
            "90225": "確定", "44002": "取消", "90224": "花費@0？",
            "44000": "贈送給@0？", "44001": "贈送",
            "20308": "確定", "20307": "全部使用", "20296": "取消",
            "20215": "是否使用@0？", "90089": "是否使用@0？",
            "90015": "提示", "90030": "是否消耗@0？", "20129": "取消",
            "20309": "全部使用", "90226": "提示", "90227": "確定",
            "10084": "是否使用@0？", "10040": "是否消耗@0？",
            "90088": "花費@0@1購買@2次？剩餘@3次", "90670": "點券",
            "90087": "次數已滿@0", "10135": "操作失敗",
            "20324": "每日簽到", "20323": "簽到", "20311": "獲得",
            "20163": "金幣", "20164": "點券", "90466": "鑽石",
            "90586": "碎片", "90672": "已擁有", "90673": "未擁有",
            "20379": "勳章", "90186": "魂石", "20429": "體力",
            "90187": "競技點", "90562": "公會貢獻", "90593": "獎勵已發放",
            "97813": "公會幣", "90792": "裝備碎片", "98028": "天賦點",
            "96567": "團購幣", "90173": "領取", "90176": "全部領取",
            "90175": "取消", "90159": "花費@0？", "90442": "重置",
            # Generic current/max counter used by PVE star displays and the
            # barracks header.  "當前…下一級…" was wrong there.
            "90525": "@0/@1",
            "90626": "火", "90627": "水", "90628": "風", "90629": "雷",
            "90630": "光", "90631": "暗", "90632": "毒", "90633": "冰",
            "90634": "岩", "90635": "風刃", "90636": "雷電",
            "90637": "單體", "90638": "群體", "90639": "持續",
            # 戰鬥狀態 / 飄字 (Avatar).  Original single-player labels; the
            # battle pixel font only covers its original vocabulary.
            "30019": "沉默", "30037": "的", "30015": "虚弱",
            "30038": "中毒", "30028": "灼烧", "30017": "破防",
            "30018": "眩晕", "30025": "抵消", "30020": "无效",
            "30002": "回合", "30013": "中毒", "30012": "盾",
            "30014": "力", "30082": "钢铁", "30027": "嘲讽",
            "30016": "净化", "30080": "诅咒", "30081": "神佑",
            "30010": "闪避", "30000": "+", "30029": "免疫",
            "30060": "反击", "30061": "复仇", "30011": "暴击",
            "30004": "克",
            # 主界面頂欄
            "20493": "體力", "90403": "競技體力", "90241": "體力@0/@1",
            "20013": "恢復@0", "96000": "體力恢復中",
            "20231": "經驗已滿", "20134": "距離升級還需@0經驗",
            "20167": "區服：@0", "20168": "賽季：@0",
            "20132": "公會", "20133": "競技", "20187": "VIP@0",
            "20188": "VIP經驗@0", "20189": "距升級還需@0",
            # 副本章節 / 關卡
            "20253": "普通", "20254": "困難", "20029": "活動",
            "20028": "章", "90404": "請先通關@0", "90244": "章節獎勵",
            "90239": "領取", "90245": "獎勵已領取", "90033": "獲得@0點券",
            "20032": "消耗@0體力", "20031": "次數@0", "20033": "進入",
            "97684": "需要VIP@0", "25042": "推薦戰力",
            "25043": "推薦等級", "25044": "推薦隊伍",
            "20177": "戰力@0/@1", "20178": "勝率@0", "90090": "獎勵",
            "97685": "VIP等級不足", "90052": "體力不足",
            # 任務獎勵
            "20136": "進度@0/@1", "20130": "剩餘時間@0",
            "90124": "已達最高等級@0", "90183": "是否領取獎勵？",
            "90219": "消耗@0金幣兌換？", "90223": "需要@0",
            "90229": "消耗@0魂石？", "90222": "需要@0好友",
            "90230": "消耗@0點券洗煉？", "90235": "通關@0",
            "90236": "通關@0", "90237": "通關@0", "20216": "獎勵已領取",
            # 祭壇
            "20063": "金幣祭壇", "20064": "點券祭壇",
            # PanelCasinoA prints config[14]-based countdown above the single
            # draw button: 0 -> "再抽10次可免費", ... -> "免費".
            "90426": "再抽@0次可免費", "90445": "免費",
            "90427": "十連抽", "90384": "勝率@0", "90385": "勝率@0",
            "20490": "抽獎", "90437": "確定", "90386": "獲得@0@1",
            "90495": "勝利", "90494": "當前點券", "90013": "點券不足",
            "90424": "@0個",
            # 登入 / 帳號
            "20221": "帳號", "20222": "暱稱", "20246": "密碼",
            "20452": "修改暱稱", "20453": "綁定帳號",
            "20454": "帳號資訊", "20455": "修改密碼",
            "90659": "進入遊戲", "90709": "綁定帳號",
            "90710": "目前帳號", "90711": "綁定後可使用帳號密碼登入",
            "90152": "歡迎回到最強王者萬象版！", "90153": "請輸入帳號",
            "90154": "請輸入密碼", "90155": "帳號或密碼錯誤",
            "90156": "帳號已存在", "90177": "歡迎回來，@0",
            "90180": "遊客登入失敗，請稍後重試", "90181": "正在登入...",
            "90010": "提示", "20021": "確定", "90074": "：", "90075": "（@0）",
            "90067": "此功能暫未開放",
            # 聊天室
            "90713": "聊天室", "90715": "世界", "90714": "公會", "90716": "私聊",
            "90717": "黑名單", "90718": "今日剩餘聊天次數：@0",
            "90719": "請輸入聊天內容", "90720": "還可輸入@0字", "90721": "超出@0字",
            "97641": "聊天冷卻中，請稍後再試", "97987": "VIP玩家可無限聊天",
            "90722": "聊天內容不能為空", "90728": "已複製到剪貼簿",
            "90729": "與@0私聊：@1", "90726": "系統",
            "90737": "發送失敗，請稍後重試", "90732": "擴充聊天次數需花費@0金幣",
            "90739": "您已被禁言", "90736": "聊天對象不存在",
            "98002": "查看玩家資訊", "20140": "發送",
            # PVP 精英賽
            "90390": "32強", "90391": "16強", "90392": "8強", "90393": "4強",
            "90394": "決賽", "90357": "重新整理", "90356": "次數不足",
            "90349": "距離開始", "90350": "距離結束", "90341": "賽程",
            "90344": "距離@0開始", "90345": "比賽進行中", "90346": "比賽已結束",
            "90347": "等待下一輪比賽", "32009": "等級不足", "90361": "戰力",
            "90367": "查看粉絲", "90362": "積分",
            # 分享
            "95028": "隱私政策", "95034": "分享失敗", "95035": "分享已取消",
            "95036": "分享", "95029": "最強王者萬象版", "95030": "快來一起玩最強王者萬象版！",
            "95031": "連結", "95032": "圖片", "95033": "名稱",
            "95022": "分享失敗，請稍後重試", "95023": "分享成功",
            "95024": "分享失敗：@0", "95025": "分享錯誤：@0",
            "95026": "已複製連結", "95027": "無法分享",
            # 公會成員管理
            "97698": "任命指揮官", "97699": "任命副會長", "97700": "解除職務",
            "97701": "退出公會", "97746": "確定要任命@0為指揮官嗎？",
            "97747": "確定要退出公會嗎？", "97752": "確定要任命@0為副會長嗎？",
            "97748": "確定要解除@0的職務嗎？", "97823": "無法對自己進行此操作",
            "97751": "無法任命@0", "97749": "會長無法退出公會",
            "97753": "無法解除@0的職務", "97750": "該玩家不在線上",
            "97999": "操作失敗",
            # 公會排行 / 職位
            "97736": "公會排行", "97865": "暫無排行資料",
            "97950": "本週暫無排行資料", "97951": "排行資料尚未產生",
            "97765": "第一戰區", "97766": "第二戰區", "97767": "第三戰區",
            "97768": "第四戰區", "97769": "第五戰區", "97770": "第六戰區",
            "97771": "第七戰區", "97772": "總決賽",
            "97974": "@0排行", "97868": "@0（戰區@1）", "97949": "第@0名",
            "97867": "排行榜每5分鐘更新一次",
            "97500": "會長", "97499": "副會長", "97501": "指揮官",
            "97502": "長老", "97503": "精英", "97504": "正式成員",
            "97505": "成員", "97498": "見習成員",
            # PVP 獎勵
            "20011": "競技獎勵", "90260": "每日獎勵", "90261": "賽季獎勵",
            "90262": "排行獎勵", "90265": "競技場獎勵說明",
            "90304": "賽季結束後依排名發放獎勵", "90291": "目前排名：@0",
            "90290": "第@0名可獲得@1", "90292": "獎勵將於賽季結束後發送",
            "90334": "暫無獎勵", "90311": "第@0名：@1（@2）@3",
            "90310": "第@0名：@1（@2）@3",
            # 屬性選擇 / 強化
            "20083": "選擇獎勵", "90661": "生命", "90662": "生命+@0",
            "90663": "攻擊+@0", "90664": "防禦+@0", "90665": "戰力+@0",
            "90676": "戰力上限@0", "90666": "額外",
            # PanelBetterSelect.gotoStartBetter() passes the fed unit's star
            # as @0 (and the hero name as @1 for 90076); the gold/attribute
            # details are appended by the caller, so do not add @2.
            "90076": "吞噬@0星英雄@1？", "90016": "吞噬@0星材料？",
            "20086": "強化至@0級（共@1級）", "20084": "花費@0金幣",
            # 20075 is the warehouse capacity line used by
            # PanelSocialMainAvatar/PanelAvatarSell/PanelBetterSelect.
            "20075": "背包@0/@1",
            # 防守隊伍
            "97655": "防守隊伍", "97656": "第@0隊　戰力@1",
            "97657": "第@0隊　戰力@1", "90648": "上一隊", "98012": "下一隊",
            "98016": "切換隊伍", "98019": "下一步", "10015": "隊伍中沒有英雄",
            "98017": "請先選擇英雄", "98018": "至少需要@0名英雄",
            # 信箱
            "20049": "信箱", "20175": "系統郵件", "20174": "玩家郵件",
            "20380": "郵件保留@0天", "20143": "刪除", "20144": "領取",
            "20381": "附件已領取", "90048": "信箱已滿", "90054": "郵件不存在",
            "90130": "無法領取附件",
            # 地圖工具 / 勝利條件（原版 language_tw）
            "30030": "全面", "30031": "左", "30032": "中", "30033": "右",
            "30034": "路", "30035": "任意兩路", "30036": "、",
            "30040": "取勝", "30041": "勝利條件：", "30042": "第@0路：",
            "30043": "全殲敵方單位", "30044": "最多@0回合", "30045": "堅持到最後",
            # 裝備升級
            "90411": "裝備升級", "90444": "金幣", "90689": "升一級",
            "90517": "裝備升級說明", "90109": "升級可提升裝備屬性",
            "90110": "升級需要消耗金幣", "90111": "裝備等級不可超過角色等級",
            "90112": "升級後屬性將大幅提升", "90083": "金幣不足",
            "90084": "裝備已達最高等級", "90690": "升十級",
            "90712": "停止", "90713": "10連鍛造", "90714": "極",
            # 主介面 / 戰鬥
            "31005": "進入戰鬥", "32002": "自動戰鬥", "32005": "關閉自動戰鬥",
            "90247": "等級不足，無法進入", "31002": "等級達到@0後解鎖",
            "31003": "提升等級可解鎖更多功能", "30041": "勝利條件：",
            "98014": "下一回合", "30044": "最多@0回合",
            # 公會戰記錄
            "97802": "第@0輪", "97958": "公會：@0（@1）", "97660": "VS",
            "97963": "暫無隊伍", "97873": "暫無對戰資料",
            "97965": "暫無比賽資料", "97874": "查看比分", "97875": "戰鬥記錄不存在",
            # PVP 競猜
            "90263": "粉絲", "90275": "下注", "90276": "已下注",
            "90280": "人氣：@0", "90316": "花數：@0", "90307": "下注失敗",
            "90308": "下注成功", "90309": "比賽已結束，無法下注",
            "90315": "確定花費@0金幣下注？",
            # 公會設定
            "97778": "公會公告", "97777": "公會名稱", "97776": "公會簡介",
            "97760": "公會類型", "97761": "加入等級", "97762": "修改",
            "97818": "公會名稱不能為空", "97827": "名稱長度需在2-8字之間",
            "97788": "修改失敗",
            # 公會激勵
            "97976": "公會激勵", "97962": "鼓舞", "97977": "公會加成",
            "97978": "鼓舞記錄", "97979": "出戰隊伍",
            "97981": "鼓舞次數已用完", "97994": "確定花費@0金幣鼓舞？",
            "97975": "第@0次鼓舞需@1金幣，可獲得@2公會貢獻",
            "97989": "今日鼓舞次數已用完", "97995": "鼓舞成功",
            "97980": "鼓舞成功，全體成員戰力提升@0%，持續@1",
            # 公會戰賽程
            "97878": "公會戰賽程", "97879": "勝場：@0", "98000": "報名人數：@0",
            "97880": "本輪", "97881": "下一輪", "97882": "取消報名",
            "90256": "報名", "97990": "報名尚未開始", "97086": "報名已結束",
            "97883": "報名已截止", "97973": "需要公會人數@0人",
            "10008": "報名失敗", "97940": "更換隊伍需花費@0金幣",
            "97884": "第一輪", "97885": "第二輪", "97886": "第三輪",
            "97887": "第四輪", "97888": "第五輪", "97889": "第六輪",
            # 寶箱鑰匙
            "90531": "@0：@1", "20438": "寶箱獎勵", "20439": "開啟寶箱可獲得豐厚獎勵",
            "20440": "鑰匙可透過活動獲得", "20441": "開啟", "20442": "兌換",
            "20457": "兌換寶箱", "20443": "開啟寶箱", "90171": "鑰匙不足",
            "90172": "寶箱不足", "20510": "×", "90506": "寶箱獎勵",
            "90185": "使用鑰匙開啟寶箱可獲得獎勵", "20460": "兌換",
            "90189": "缺少@0，無法兌換@1", "90188": "消耗@0個@1可兌換@2個@3",
            # 好友
            "20004": "Lv.@0", "20053": "加好友", "20054": "已申請",
            "20055": "刪除", "90651": "線上", "90650": "離線",
            "97013": "好友列表", "97012": "確定要刪除該好友嗎？",
            "90057": "好友已滿", "20182": "確定要向@0發送好友申請嗎？",
            "90036": "對方已是好友", "90056": "無法新增自己為好友",
            # 地圖戰鬥：GameMap.getName() appends 20411 to every hard-mode
            # stage name, so it must be the difficulty tag, not 失敗.
            "20414": "勝利", "20411": "·困難", "20413": "平局",
            "32001": "@0 VS @1", "98013": "@0 VS @1　比分@2",
            "90530": "士氣高漲", "90529": "暴擊",
            "90287": "是否退出戰鬥？", "90271": "是否重新開始戰鬥？",
            "20211": "戰鬥開始",
            # 限時禮包
            "90485": "說明", "25061": "距離結束", "25060": "法防之陣貳",
            "97018": "活動已結束", "97019": "活動尚未開始", "90462": "限時禮包",
            "90416": "售價", "90417": "點券", "97010": "購買成功",
            "97009": "恭喜@0購買@1",
            # 社交郵件
            "20172": "寫信給@0", "20145": "發送", "20171": "回覆",
            "20169": "已讀",
            # 首領列表
            "90132": "擊敗首領可獲得豐厚獎勵", "20398": "擊殺", "20383": "未擊殺",
            "20399": "已攻擊@0次，造成@1傷害，排名@2，剩餘@3次，冷卻@4",
            "20365": "已攻擊@0次，造成@1傷害，排名@2，剩餘@3次，冷卻@4",
            "20376": "剩餘次數",
            # 客服中心
            "20418": "客服中心", "95015": "公告", "20456": "客服",
            "95006": "遊戲公告", "20509": "常見問題", "20204": "前往論壇",
            "97001": "今天還沒有登入遊戲哦，快回來看看吧！",
            # PVP 粉絲
            "90264": "關注", "90305": "粉絲榜說明", "90359": "粉絲數：@0",
            "90363": "鮮花：@0", "90364": "第@0名", "90365": "未上榜",
            "90314": "本場比賽粉絲貢獻",
            # DN 陣容
            # 羈絆/陣位 description templates.  PanelCenterDNTeam passes
            # (bond name, required heroes/equipment, effect[, skill name]).
            "90432": "@0：@1上陣時，增加@2",
            "90433": "@0：裝備@1時，增加@2",
            "90434": "@0：@1上陣時，獲得@2@3",
            "90435": "@0：裝備@1時，獲得@2@3",
            "90512": "已上陣：@0",
            # Equipment-detail bond text (PanelCenterDNTeam.getDestinyByEquip):
            # [bond, hero, equipment, effect] and the skill variant.
            "90446": "@0：@1裝備@2時，增加@3",
            "90447": "@0：@1裝備@2時，獲得@3@4",
            # 公會申請
            "97789": "戰力：@0", "97721": "拒絕", "95012": "同意",
            "97735": "申請已過期", "97820": "公會已滿",
            "97828": "已加入其他公會", "97829": "無法加入",
            # 版本更新 / 退出
            "100003": "版本更新", "20183": "發現新版本，請更新",
            "90681": "發現新版本，是否前往商店更新？", "90680": "更新",
            "20248": "退出遊戲",
            # 公會祈福
            "97790": "剩餘@0次", "97938": "祈福次數不足", "10009": "金幣不足",
            "97807": "消耗@0@1祈福？", "97939": "祈福失敗", "97822": "公會不存在",
            # 首領排行
            "20373": "第@0名", "20374": "傷害：@0", "90133": "排名",
            "90526": "未上榜", "20366": "傷害@0",
            # PVP 列表
            "90086": "第@0名", "90497": "戰鬥積分", "90103": "輪空",
            # 2026-10-24 arena reference UI: 換一批 / 戰報 / 競技列表.
            "98110": "挑戰", "98111": "換一批",
            "98123": "戰報", "98124": "競技列表",
            "98130": "競技場挑戰@0：@1，當前排名第@2名",
            "98131": "暫無戰報",
            "90119": "王者@0", "90118": "王者@0-@1",
            # 好友搜尋
            "20050": "UID：@0", "20051": "輸入UID搜尋玩家", "20052": "搜尋",
            "90050": "找不到該玩家", "90049": "UID不能為空", "90037": "無法搜尋自己",
            # 社交郵箱
            "20141": "收到", "20142": "發送", "97006": "第@0頁",
            "90038": "暫無郵件", "90026": "請選擇郵件",
            # 兌換
            "90388": "兌換", "20301": "時間：@0", "20302": "數量：@0",
            "90281": "VIP@0可兌換", "90125": "確定花費@0勳章兌換@1？",
            "90106": "勳章不足",
            # 改名
            "20305": "改名", "90093": "目前名稱：@0", "90094": "改名需花費@0點券",
            "90288": "名稱不能為空", "90107": "確定將名稱@0改為@1？",
            "90095": "名稱@0已被使用",
            # 探險地圖
            "90589": "探險", "90669": "是否進入探險？", "90616": "次數不足",
            "90619": "提示", "90618": "消耗@0金幣繼續探險？", "90561": "探險完成",
            # 聊天對象設定
            "90723": "玩家資訊", "90724": "查看資料", "90725": "加入黑名單",
            "90730": "已加入黑名單", "90734": "確定要加入黑名單嗎？",
            "90735": "已從黑名單移除",
            # 限時抽取
            "97070": "活動說明", "97075": "活動可獲得@0", "97072": "活動積分：@0",
            "97071": "免費抽取", "97074": "倒數@0", "97661": "抽取",
            # 公會面板
            "97937": "查看", "97825": "退會懲罰剩餘@0",
            "97821": "尚未加入公會", "97923": "無法查看",
            # 物品基礎
            # 20017 wraps the level number: non-max shows "LV.N", while the
            # max-level branch substitutes 20180 so the tile reads "LV.MAX".
            "20015": "數量", "10134": "剩餘", "20017": "LV.@0",
            "20181": "@0", "20180": "MAX",
            # PVP 排行
            "97654": "@0（@1）", "98021": "排名", "98032": "挑戰失敗",
            "98020": "次數不足",
            # 公會玩家設定
            "90747": "已發送好友申請",
            # 支付
            "20223": "確定", "90066": "購買失敗，請稍後重試",
            "90060": "付款失敗", "90039": "提示", "90040": "是否聯絡客服？",
            # 幫助
            "20249": "確定", "20250": "取消", "90072": "幫助", "20251": "取消",
            "90045": "是否退出遊戲？",
            # 首領結算
            "90408": "首領戰結束", "20367": "首領@0剩餘生命@1，已攻擊@2次，獲得@3金幣@4",
            "20378": "獎勵已發送至信箱", "90528": "極限傷害獎勵",
            "20384": "未參與戰鬥",
            # 社交主頁
            "97005": "背包", "90548": "暫無好友", "90077": "刪除好友@0？",
            "90055": "確定刪除@0？", "90009": "操作成功",
            # 下注 / 送花
            "90395": "下注", "90282": "下注說明", "90371": "下注成功",
            "90370": "下注@0金幣，可獲得@1金幣", "90372": "金幣不足",
            "90396": "送花", "90285": "贈送鮮花說明", "90374": "送花成功",
            "90373": "贈送@0朵鮮花，花費@1金幣", "90375": "獲得獎勵",
            # 探險選隊
            "90667": "探險", "90612": "英雄@0已在探險中", "90613": "請先選擇英雄",
            "90576": "隊伍已滿", "90614": "探險隊伍不能為空",
            # 培育
            "90577": "培育手冊", "90643": "培育說明", "90674": "培育",
            "90678": "是否消耗培育手冊？", "90677": "每次培育可提升屬性",
            # 時間格式
            "98022": "秒", "98023": "分", "98024": "小時", "98025": "天",
            "98026": "月", "98027": "年",
            "20478": "天", "20479": "小時", "20480": "分", "20481": "秒",
            "20482": "剛剛", "20487": "分", "20488": "時",
            # 跨服 PVP
            "96563": "戰鬥", "96568": "距離結束", "98055": "距離開始",
            "98060": "巔峰戰場", "98061": "榮耀競技場", "98062": "王者之巔",
            "96560": "報名中", "90805": "參賽次數：@0",
            # 公會祈福獎勵
            "97809": "公會祈福獎勵", "97811": "公會祈福金：@0", "97812": "領取",
            "97824": "無可領取獎勵", "97636": "獲得@0金幣",
            # 公會戰記錄
            "97872": "暫無記錄", "97871": "本輪暫無記錄", "97870": "比賽尚未開始",
            "97799": "第@0輪　戰區@1", "97800": "勝場：@0",
            # 公會戰賽程項目
            "97905": "輪空", "97895": "輪空", "97916": "已淘汰",
            "97899": "VS", "97900": "戰區@0",
            # 公會戰獎勵 / 戰區
            "97944": "查看獎勵", "97945": "第@0劇場", "97946": "戰區@0",
            "97947": "全服", "97948": "跨服",
            # PVE 隊伍
            "20030": "隊伍等級@0", "90047": "體力不足",
            "20275": "@0已出戰", "20217": "請先選擇隊伍",
            # 晶片
            "90658": "晶片", "20437": "晶片", "90184": "晶片可提升英雄屬性",
            "20430": "能量@0/@1", "90515": "碎片屬性", "90516": "能量@0/@1",
            "90413": "合成", "90409": "主动技能", "30001": "級", "90410": "主动",
            # PVP 戰鬥獎勵
            "90320": "勝利", "90321": "失敗", "90322": "平局", "90323": "輪空",
            # 獎勵預覽
            "98051": "每日獎勵", "98052": "累計獎勵", "96561": "第@0天",
            "96569": "已領取",
            # 公會解散
            "97831": "剩餘人數@0", "97755": "解散公會", "97756": "無法解散公會",
            "97817": "確定要解散公會嗎？剩餘@0人",
            # 公會排行項目
            "97910": "第@0名", "97955": "@0（@1）", "97956": "積分：@0",
            "97957": "戰力：@0",
            # 裝備選擇
            "20274": "選擇", "10130": "隊長已裝備", "10131": "隊員@0已裝備",
            # 巔峰之戰
            "96564": "巔峰之戰", "98015": "至少需要@0名英雄", "10132": "請先選擇英雄",
            # 英雄選擇 / 命名
            "20001": "選擇英雄", "90418": "下一步", "20306": "隨機",
            "90421": "選擇名稱", "90422": "確定",
            # PVE 好友助戰
            "20035": "好友助戰", "90242": "好友助戰說明", "90243": "確定",
            "20139": "普通攻擊", "20037": "無技能", "20036": "次數@0/@1",
            # 社交中心
            "20047": "好友", "20046": "郵件", "20045": "搜尋",
            # 設定
            "20119": "設定", "20122": "音樂", "20123": "音效",
            # 任務獎勵
            "20155": "任務", "20252": "已領取", "20428": "領取",
            # 聊天項目
            "90741": "世界", "90740": "私聊", "20206": "（@0）",
            # 兌換商店
            "20298": "兌換商店", "20299": "兌換說明", "90496": "兌換",
            # 英雄進化
            "20467": "進化", "90228": "進化可提升英雄屬性",
            "90213": "@0可進化至最高@1級，領導力@2",
            # 編隊
            "25062": "上陣", "25063": "下陣", "25022": "更換",
            # DN 詳情
            "90448": "DN說明", "25036": "升級", "25037": "重置",
            # 進化選擇
            "90217": "材料不足", "90216": "該英雄無法進化", "90218": "@0已上陣",
            # 參悟
            "90519": "參悟說明", "90238": "點券不足", "90457": "裝備不足",
            "90389": "PVP精英賽", "90254": "第@0屆", "90377": "報名時間：@0",
            "90412": "選擇參悟材料", "90414": "已選擇@0/@1", "90415": "材料@0/@1",
            # 洗煉
            "90518": "洗煉說明", "90522": "洗煉可提升屬性", "90523": "洗煉需要消耗點券",
            # 探險確認
            "90555": "探險", "90603": "探險消耗", "90602": "消耗@0金幣繼續探險？",
            # 公會升級
            "90769": "公會升級", "90783": "下級效果", "90802": "公會@0可升級",
            # 公會申請
            "97682": "申請加入公會", "97683": "公會人數@0/@1",
            "97722": "申請後請等待會長審核",
            # 積分兌換
            "97997": "需要積分", "97998": "活動未開啟", "97694": "積分不足",
            # 公會列表
            "97784": "公會已滿", "97970": "已加入其他公會", "97968": "等級不足",
            # 編隊英雄
            "90511": "該英雄已在隊伍中",
            # 雜項 UI
            "10128": "請選擇裝備", "10150": "獲得@0×@1", "20020": "資訊",
            "98031": "勝場", "20058": "賭場", "20101": "英雄幫助",
            "20100": "遊戲公告", "20102": "音效設置", "20159": "退出",
            "90852": "英雄圖鑑", "90853": "隊伍中",
            "90854": "極限突破", "90855": "請放入神眷秘寶",
            "90856": "關於開發者", "90857": "開發者的信",
            # 2026-10-25: Turso account login screen.
            "90858": "帳號", "90859": "密碼", "90860": "註冊",
            "90861": "請輸入帳號與密碼", "90862": "帳號或密碼錯誤",
            "90863": "註冊失敗", "90864": "帳號長度需為 2-20 個字元",
            "90865": "密碼長度需為 4-64 個字元", "90866": "帳號已存在",
            "90867": "註冊成功",
            # 2026-10-25: login/register panel v2 (账号 4-16 位字母数字).
            "90868": "請輸入帳號", "90869": "請輸入密碼",
            "90870": "帳號僅支持字母和數字，長度 4-16 位",
            "90871": "密碼長度至少 6 位",
            "90872": "該帳號已存在，請換一個帳號",
            "90873": "帳號不存在",
            "90874": "登入", "90875": "登入", "90876": "前往註冊",
            "90877": "註冊", "90878": "設定帳號", "90879": "設定密碼",
            "90880": "確認註冊", "90881": "返回登入",
            "90882": "登入已過期，請重新登入",
            "90883": "退出登錄", "90884": "確定退出當前帳號？",
            "90885": "已登入：@0",
            "20388": "@0幫助", "90438": "載入中...", "20103": "幫助",
            "20113": "戰鬥結算", "20120": "關閉", "20121": "確定",
            "20108": "戰鬥結果",
            "90127": "確定要刪除嗎？", "20124": "英雄升星", "20125": "英雄突破",
            "20218": "兌換碼", "20219": "請輸入兌換碼", "20310": "功能未開放",
            "20433": "未滿", "20434": "PK", "20466": "選擇遠征隊伍",
            "90708": "遠征說明", "20474": "統御力", "90012": "達到@0級解鎖",
            "25059": "第@0頁", "30105": "原價@0點券", "31004": "點擊繼續",
            "32003": "勝利", "32004": "失敗", "32008": "戰鬥失敗",
            "90025": "暫無好友申請", "90688": "獎勵", "90058": "提示：@0",
            "90091": "裝備已鎖定", "90126": "需要開啟@0功能",
            "90537": "功能尚未開放", "90453": "已結束",
            "90134": "擊敗@0，耗時@1",
            "90206": "強化+@0，消耗@1金幣，成功率@2%，獲得@3",
            "90207": "附魔成功", "90211": "請選擇要出售的裝備$品質$數量",
            "90214": "進化可提升英雄屬性", "90246": "請選擇進化材料",
            "90283": "已結束", "90284": "進行中", "90293": "心情：@0",
            "90294": "獎勵已領取", "90296": "獎勵", "90317": "觀戰",
            "90348": "剩餘@0次", "90405": "傷害排名", "90406": "點券",
            "90407": "返回", "97662": "再抽一次", "90419": "VIP特權",
            "90423": "鎖定：@0", "90450": "遠征獎勵", "90459": "限時禮包詳情",
            "90520": "領取失敗", "90534": "客服：@0", "90535": "我的客服",
            "90541": "客服服務時間：@0", "90551": "已加入探險",
            "90574": "探險隊伍已滿", "90731": "黑名單為空",
            "90733": "花費點券可解除禁言",
            "90738": "網路連線中斷，請重新登入",
            "90784": "選擇替換成員", "90785": "請選擇要替換的成員",
            "95010": "前往儲值", "95013": "公告內容", "95014": "公告內容",
            "96562": "排名", "98033": "第@0名", "97057": "第@0天獎勵",
            "97085": "活動積分", "97996": "積分", "97608": "功能開放",
            "97609": "功能：@0", "97610": "查看", "97693": "積分：@0",
            "97717": "修改公會圖示", "97730": "加入時間：@0",
            "97922": "職位：@0", "97758": "請輸入公會公告",
            "97787": "公告不能為空", "97876": "第@0輪比分",
            "97877": "參戰人數：@0", "97892": "冷卻中", "97894": "公會擊殺首領數",
            "97901": "Lv.@0", "97904": "傷害：@0", "97907": "首領尚未出現",
            "98001": "今日擊殺次數已用完", "97924": "積分：@0",
            "97925": "VIP祭壇：點券抽取進階/UP英雄（本期：%s），10抽保底5星與材料，50抽保底6星。"
                     % HERO_NAMES.get(_UP_FAMILY, "費德提克"),
            "97986": "第@0輪獎勵",
            "97943": "第@0輪　戰區@1", "97969": "獎勵預覽",
            "97983": "暫無公會加成", "97984": "暫無鼓舞記錄",
            "97985": "@0%", "97991": "第@0名",
            "97988": "@0（@1）使用@2，效果@3", "98029": "對戰記錄",
            "98030": "第@0場", "98034": "記錄不存在",
            # 系統郵件 (user.get_msg / gift_msg) titles.
            "99001": "系統郵件", "99002": "系統補償",
            "99003": "英雄升級資源補給",
            # Title that echoes info_data verbatim (family test packages).
            "99004": "@0",
        },
        # Per-stage battle maps (GameMapData); see _combat_main() below.
        "combat_main": _combat_main(),
        # PanelCenterTaskAward.checkTaskComplete() indexes these directly.
        # task[key].content = [{gift:{type:amount}, need:N|mapId}, ...]
        "task": {
            "login_total": {
                "need_lv": 1, "info": 91001, "index": 1,
                "begin_time": datetime.datetime.utcnow(),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=3650),
                "content": [
                    {"gift": {"gold": 500}, "need": 1},
                    {"gift": {"gold": 1000}, "need": 3},
                ],
            },
            "pass_map_main": {
                "need_lv": 1, "info": 91002, "index": 2,
                "begin_time": datetime.datetime.utcnow(),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=3650),
                "content": [
                    {"gift": {"gold": 800}, "need": "M_011_1"},
                    {"gift": {"gold": 1200}, "need": "M_012_1"},
                ],
            },
            "level_up": {
                "need_lv": 1, "info": 91003, "index": 3,
                "begin_time": datetime.datetime.utcnow(),
                "end_time": datetime.datetime.utcnow()
                + datetime.timedelta(days=3650),
                "content": [
                    {"gift": {"gold": 1000}, "need": 26},
                ],
            },
        },
        # 2026-10-24 daily welfare (task tab row): 30,000 點券 + 1,000,000 金幣.
        "everyday_gift": [
            {"coin": 30000, "gold": 1000000},
        ],
        # PanelEveryDaySign reads cfg.check_in (root), not system_simple's.
        "check_in": dict({"open_status": 1}, **_check_in_cfg()),
        # PVE tab 3 (活动副本 / 经营副本): gold, exp, energy and equipment
        # trials.  battle_ploy is the list; combat_ploy holds the maps.
        "battle_ploy": _battle_ploy_cfg(),
        "combat_ploy": _activity_combat(),
    }
    # 負面測試 enemies cast one whole-team debuff each (see
    # _test_debuff_stage_map / _DEBUFF_TEST_SKILLS).
    cfg["skill"].update(_debuff_test_skill_cfg())
    # 484 avatar ids from the client icon atlases, plus our hand-written
    # story heroes / sign-plant display ids.
    cfg["avatar"] = _merge_avatars(cfg["avatar"], cfg["skill"])
    # Test-stage-only enemy templates (fixed 5e8/1e9 HP, 1000 attack).
    cfg["avatar"].update(_test_enemy_avatar_entries())
    # 40-chapter gatekeepers: enemy-only 6★ boss copies of advanced heroes.
    cfg["avatar"].update(_pve_boss_avatar_entries(cfg["avatar"]))
    # SkillSet.getInfoDetails() appends skillSetData.info verbatim and
    # prints the literal string "null" when a combat skill has no info.
    # Give each skill a short description derived from its first action.
    _SKILL_INFO = {
        "damage": "對敵方造成傷害", "combo": "連續攻擊敵方",
        "stun": "眩暈敵方", "silence": "沉默敵方",
        "suck": "吸取敵方生命", "pull": "將敵方拉近",
        "push": "擊退敵方", "dash": "衝向敵方",
        "cure": "恢復友方生命", "shield": "為友方施加護盾",
        "purify": "淨化友方負面效果", "summon": "召喚援軍",
        "strong": "提升自身能力", "reline": "突進至敵方後排",
        "poison": "使敵方中毒",
    }
    for _sk in cfg["skill"].values():
        # SkillSet.init() with slv > 1 does
        #   skills = clone(skillSetData.skills)
        #   skills[skillUp[0]][1] += skillUp[1] * (lv - 1)
        # A skillUp index past the action list (the original S_1008..S_1017
        # data uses index 2 on 1–2 action skills) dereferences undefined and
        # throws #1010 as soon as the barracks builds an Avatar whose
        # _ensure_avatars-granted slv is greater than 1.
        _acts = _sk.get("skill") or []
        _su = _sk.get("skillUp")
        if _acts and isinstance(_su, list) and _su:
            try:
                _idx = int(_su[0])
            except (TypeError, ValueError):
                _idx = 0
            if _idx < 0 or _idx >= len(_acts):
                _su[0] = max(0, min(_idx, len(_acts) - 1))
        if _sk.get("info"):
            continue
        for _act in _acts:
            if _act and _act[0] in _SKILL_INFO:
                _sk["info"] = _SKILL_INFO[_act[0]]
                break
        else:
            _sk["info"] = "技能效果"
    return cfg


def new_account(uid, pw):
    return {
        "uid": uid,
        "sessionid": pw,
        "session_key": uid,
        "nick": uid,
        "level": 1,
        # PVE progress (persisted across logins)
        "cid": PVE_STAGE_ORDER[0],
        "cleared": {},
        "gold": 0,
        "lv": 25,
        "exp": 0,
        "combat_score": empty_combat_score(),
        "dust_arr": [99999, 99999, 99999, 99999, 99999],
        "dust_seeded_v2": True,
    }


# Story order used by next_stage() and reward scaling: 40 chapters x 4.
PVE_STAGE_ORDER = [
    "M_%03d_%d" % (PVE_FIRST_CHAPTER + chapter, stage)
    for chapter in range(PVE_CHAPTER_COUNT)
    for stage in range(1, PVE_STAGES_PER_CHAPTER + 1)
]


# 2026-10-24: bot lineups are built exclusively from the novice pool
# (gallery 1-21 + 127-141) and the advanced pool (gallery 22-32, 37,
# 39-42, 49, 51-53, 57, 59, 60, 62, 67, 68, 75, 108).  Materials,
# monsters and buildings never appear in arena/ranked teams.
PVP_NOVICE_FAMILIES = [
    "A_1001", "A_1002", "A_1003", "A_1004", "A_1005", "A_1006",
    "A_1007", "A_1008", "A_1009", "A_1010", "A_1011", "A_1012",
    "A_1013", "A_1014", "A_1015", "A_1016", "A_1017", "A_1018",
    "A_1019", "A_1020", "A_1021",
    "A_1900", "A_1901", "A_1902", "A_1903", "A_1904", "A_1905",
    "A_1906", "A_1907", "A_1908", "A_1909", "A_1910",
    # 2026-10-24: A_1996-A_1999 are event/placeholder cards whose card art
    # does not survive ItemPVP's ListDataViewPort (#3663 undefined texture),
    # so keep them out of arena/ranked bot lineups.
]
PVP_ADVANCED_FAMILIES = list(PVE_ADVANCED_HEROES)


def _hero_gallery_list():
    """Ordered card ids for the 英雄圖鑑 panel.

    novice (gallery 1-21 + 127-141) -> advanced (28 families) -> the seven
    UP heroes, which always sit at the end.
    """
    fams = list(PVP_NOVICE_FAMILIES)
    for fam in ("A_1996", "A_1997", "A_1998", "A_1999"):
        if fam not in fams:
            fams.append(fam)
    fams += list(PVP_ADVANCED_FAMILIES)
    fams += list(_UP_ROTATION)
    out = []
    seen = set()
    for fam in fams:
        if fam in seen:
            continue
        seen.add(fam)
        out.append(_pvp_hero(fam, 6))
    return out


def _pvp_hero(fam, star):
    """Resolve a family to the highest available card at/under `star`.

    Never return the synthesized 7★ card: ItemPVP builds its own Avatar from
    data_base and the 7★ red card frame path leaves a null texture in the
    ListDataViewPort (#3663 Sampler 0 binds an undefined texture).
    """
    star = int(star)
    for s in range(star, 0, -1):
        sid = "%s_%d" % (fam, s)
        if sid in AVATAR_CATALOG:
            return sid
    for s in (6, 5):
        sid = "%s_%d" % (fam, s)
        if sid in AVATAR_CATALOG:
            return sid
    return "%s_5" % fam


def _pvp_bot_team(fams, star, lv):
    return [(_pvp_hero(fam, star), lv) for fam in fams]


# 競技場 opponents.  ids intentionally lack the "r" marker so ItemPVP uses
# the supplied data_base instead of looking the team up in cfg.pvp_robot.
PVP_BOTS = [
    {"uid": "bot_pvp_01", "name": "荒原狼騎", "lv": 22, "offset": -12,
     "team": _pvp_bot_team(
         ["A_1001", "A_1002", "A_1003", "A_1004", "A_1005"], 5, 22)},
    {"uid": "bot_pvp_02", "name": "暗影刺客", "lv": 23, "offset": -8,
     "team": _pvp_bot_team(
         ["A_1006", "A_1007", "A_1008", "A_1009", "A_1010"], 5, 23)},
    {"uid": "bot_pvp_03", "name": "深淵術士", "lv": 24, "offset": -4,
     "team": _pvp_bot_team(
         ["A_1011", "A_1012", "A_1013", "A_1014", "A_1015"], 5, 24)},
    {"uid": "bot_pvp_04", "name": "星界遊俠", "lv": 25, "offset": -1,
     "team": _pvp_bot_team(
         ["A_1016", "A_1017", "A_1018", "A_1019", "A_1020"], 5, 25)},
    {"uid": "bot_pvp_05", "name": "王者侍衛", "lv": 25, "offset": 1,
     "team": _pvp_bot_team(
         ["A_1022", "A_1023", "A_1024", "A_1025", "A_1026"], 5, 25)},
    {"uid": "bot_pvp_06", "name": "雷霆戰神", "lv": 26, "offset": 4,
     "team": _pvp_bot_team(
         ["A_1027", "A_1028", "A_1029", "A_1030", "A_1032"], 5, 26)},
    {"uid": "bot_pvp_07", "name": "永夜君王", "lv": 27, "offset": 8,
     "team": _pvp_bot_team(
         ["A_1033", "A_1049", "A_1053", "A_1054", "A_1056"], 6, 27)},
    {"uid": "bot_pvp_08", "name": "最強王者", "lv": 28, "offset": 12,
     "team": _pvp_bot_team(
         ["A_1060", "A_1078", "A_1081", "A_1082", "A_1083"], 6, 28)},
]

# Pool used to build a fresh set of arena teams for user.refresh_pvp_opponents.
_PVP_BOT_POOL = [
    _pvp_hero(fam, 5 if fam in PVP_NOVICE_FAMILIES else 6)
    for fam in (PVP_NOVICE_FAMILIES + PVP_ADVANCED_FAMILIES)
]


# --------------------------------------------------------------------------- #
# Cross-server ranked PVP (PVP tab 4 / PanelPVP15)
# --------------------------------------------------------------------------- #
_SPVP_ROSTER = [
    _pvp_hero(fam, 5 if fam in PVP_NOVICE_FAMILIES else 6)
    for fam in (PVP_NOVICE_FAMILIES + PVP_ADVANCED_FAMILIES)
]


def _make_spvp_bots():
    """15-avatar (3 teams x 5) ranked opponents from the hero pools."""
    bots = []
    pool = _SPVP_ROSTER
    for i, base in enumerate(PVP_BOTS):
        team = []
        for j in range(15):
            aid = pool[(i * 15 + j) % len(pool)]
            team.append((aid, max(16, int(base["lv"]) - 2 + (j % 3))))
        bots.append({
            "uid": "bot_spvp_%02d" % (i + 1),
            "name": base["name"],
            "lv": base["lv"],
            "rank": i + 1,
            "zone": "1-01",
            "teams": [team[0:5], team[5:10], team[10:15]],
        })
    return bots


SERVER_PVP_BOTS = _make_spvp_bots()


def _pvp_level_shift(acc):
    """Scale bot levels with the player's account level (arena + ranked)."""
    try:
        lv = int((acc or {}).get("lv", 25))
    except (TypeError, ValueError):
        lv = 25
    return max(0, min(50, lv - 25))


def _pvp_bots_for(acc):
    shift = _pvp_level_shift(acc)
    batch = int((acc or {}).get("pvp_batch", 0) or 0)
    out = []
    for i, bot in enumerate(PVP_BOTS):
        nb = dict(bot)
        nb["lv"] = int(bot["lv"]) + shift
        if batch:
            rng = random.Random(batch * 10007 + i * 131)
            aids = rng.sample(_PVP_BOT_POOL, 5)
            nb["team"] = [(aid, int(bot["lv"]) + shift) for aid in aids]
        else:
            nb["team"] = [(aid, int(lv) + shift) for (aid, lv) in bot["team"]]
        out.append(nb)
    return out


def _pvp_daily_count(acc):
    """Number of rewarded arena battles today (client shows X/10)."""
    today = datetime.date.today().isoformat()
    if acc.get("pvp_day") != today:
        acc["pvp_day"] = today
        acc["pvp_day_count"] = 0
    try:
        return int(acc.get("pvp_day_count", 0))
    except (TypeError, ValueError):
        return 0


def _pvp_mark_for_rank(rank):
    pc = _cfg()["system_simple"]["pvp_config"]
    try:
        return max(1, int(
            (float(pc[6]) / (rank + float(pc[7]))) ** float(pc[8])
            + float(pc[9])))
    except Exception:                       # noqa: BLE001
        return 1


def _arena_rank_payload(acc):
    """[my_rank, entries, [], [], [], mark, daily_reward_battles]."""
    my_rank = int(acc.get("pvp_rank", 300))
    bots = _pvp_bots_for(acc)
    # Keep every opponent on a distinct rank.  A player parked at the top of
    # the ladder (rank 1) would otherwise clamp every my_rank+offset to 1
    # and the whole list would read 第1名.
    anchor = max(my_rank, len(bots) + 4)
    used = {my_rank}
    entries = []
    for bot in sorted(bots, key=lambda b: int(b["offset"])):
        rank = max(1, anchor + int(bot["offset"]))
        while rank in used:
            rank += 1
        used.add(rank)
        entries.append([rank, bot["uid"], bot["name"],
                        _pvp_data_base(bot), int(bot["lv"]),
                        _pvp_mark_for_rank(rank)])
    return [my_rank, entries, [], [], [], int(acc.get("mark", 0)),
            _pvp_daily_count(acc)]


def _spvp_bots_for(acc):
    shift = _pvp_level_shift(acc)
    out = []
    for bot in SERVER_PVP_BOTS:
        nb = dict(bot)
        nb["lv"] = int(bot["lv"]) + shift
        nb["teams"] = [[(aid, int(lv) + shift) for (aid, lv) in team]
                       for team in bot["teams"]]
        out.append(nb)
    return out


def _spvp_bot_by_uid(uid, acc=None):
    bots = _spvp_bots_for(acc) if acc is not None else SERVER_PVP_BOTS
    for bot in bots:
        if bot["uid"] == uid:
            return bot
    return bots[0]


def _spvp_team_rows(teams):
    return [[[aid, int(lv), None] for (aid, lv) in team]
            for team in teams]


def _squad_cell_key(cell):
    """Normalize a defense-team cell to an avatar instance key."""
    if isinstance(cell, (list, tuple)):
        return str(cell[0]) if cell and cell[0] else ""
    if isinstance(cell, str):
        return cell
    return ""


def _normalize_squad(squad):
    """3x5 cells; each occupied cell is [key], empty cells are "".

    PanelDefenseTeam / PanelPVP15RankIn / PanelActivityPVPBattleOfThePeak
    all read cell[0], so cells must be arrays, not bare strings.
    """
    rows = []
    for row in (squad or [])[:3]:
        cells = []
        for cell in list(row or [])[:5]:
            key = _squad_cell_key(cell)
            cells.append([key] if key else "")
        cells += [""] * (5 - len(cells))
        rows.append(cells)
    while len(rows) < 3:
        rows.append([""] * 5)
    return rows


def _spvp_squad_rows(acc, squad):
    """Expand a normalized defensive_squad for display."""
    avatars = _ensure_avatars(acc)
    rows = []
    for team in _normalize_squad(squad):
        row = []
        for cell in team:
            key = _squad_cell_key(cell)
            if not key:
                row.append(None)
                continue
            aid = key.split("|")[0]
            av = avatars.get(key) or avatars.get(aid) or {}
            row.append([aid, int(av.get("lv", 1)), None])
        rows.append(row)
    return rows


def _default_defensive_squad(acc):
    avatars = _ensure_avatars(acc)
    # Only kind-1 heroes can be fielded: checkSearchTypeByType(...,1)
    # rejects materials, and a mismatch between the saved squad and the
    # client's team slots makes PanelDefenseTeam think nothing was selected.
    keys = [k for k in avatars
            if int(AVATAR_CATALOG.get(k.split("|")[0], {}).get("kind", 1))
            == 1]
    keys.sort(key=lambda k: (-int(avatars[k].get("lv", 1)), k))
    if not keys:
        return [[""] * 5 for _ in range(3)]
    # The client needs at least two heroes in every 15v15 team.  Small
    # rosters repeat their best heroes across the three defense teams so the
    # mode is playable from the start.
    keys = (keys * 3)[:15]
    squad = [[[key] for key in keys[t * 5:(t + 1) * 5]] for t in range(3)]
    return _normalize_squad(squad)


def _spvp_my_team_entries(acc, keys):
    avatars = _ensure_avatars(acc)
    out = []
    for cell in list(keys or [])[:5]:
        key = _squad_cell_key(cell)
        if not key:
            continue
        aid = key.split("|")[0]
        av = avatars.get(key) or avatars.get(aid) or {}
        out.append((aid, int(av.get("lv", 1))))
    return out


def _spvp_units(entries, side):
    """Battle units for the 2-lane 巔峰之戰 map (line must be 0/1)."""
    units = _pvp_units(entries, side)
    for i, unit in enumerate(units):
        unit["line"] = i % 2
        if side == 1:
            unit["pos"] = int((0.22 + 0.12 * (i // 2)) * 3000)
        else:
            unit["pos"] = int((0.70 + 0.12 * (i // 2)) * 3000)
        unit["leader"] = 1 if i == 0 else 0
    return units


def _avatar_power(aid, lv):
    """Rough combat power from cfg.avatar, used to predict arena outcomes."""
    av = _cfg()["avatar"].get(aid) or {}
    pl = av.get("pl") or [500, 40, 200, 12, 100, 3, 100, 3, 300, 250]
    hp = pl[0] + pl[1] * lv
    ap = pl[2] + pl[3] * lv
    defense = (pl[4] + pl[5] * lv) + (pl[6] + pl[7] * lv)
    return hp * 0.5 + ap * 2 + defense * 0.625


def _team_power(entries):
    return sum(_avatar_power(aid, lv) for (aid, lv) in entries)


def _pvp_bot_by_uid(uid, acc=None):
    bots = _pvp_bots_for(acc) if acc is not None else PVP_BOTS
    for bot in bots:
        if bot["uid"] == uid:
            return bot
    return bots[0]


def _pvp_data_base(bot):
    """Display-only team arrays for ItemPVP ([aid,lv,slv,hp,ap,...])."""
    return [[aid, lv, 1, 0, 0, 0, 0, 0, None, None, None, 0]
            for (aid, lv) in bot["team"]]


def _pvp_units(entries, side):
    """client_orgin_team_* units; the client builds full Avatars from cfg."""
    units = []
    count = max(1, len(entries))
    for i, (aid, lv) in enumerate(entries):
        unit = _make_avatar(aid, lv)
        # 2026-10-24: match the PVE layout — our team at the bottom of the
        # lane (pos 0.72/0.78/0.84) and the whole enemy team at the very top
        # (pos 0.10/0.16/0.22).  pos maps to screen y (0 = top).
        base = 0.72 if side == 1 else 0.10
        step = 0.06
        pos = min(0.995, base + (i // 3) * step)
        unit.update({
            "aid": aid,
            "line": i % 3,
            "pos": int(pos * 3000),
            "leader": 1 if i == 0 else 0,
        })
        units.append(unit)
    return units


def _exploration_row(aid, lv, slv=1):
    """NPC-style avatar row used by PanelActivityExplorationMyTeam.

    AvatarImg(..., isArray=true, isNpc=true) reads [0]=aid, [1]=lv,
    [2]=slv, [6]=current hp, [7]=max hp.
    """
    av = _cfg()["avatar"].get(aid) or {}
    pl = av.get("pl") or [500, 40, 200, 12, 100, 3, 100, 3, 300, 250]
    hp = int(pl[0] + pl[1] * int(lv))
    row = [0] * 16
    row[0] = aid
    row[1] = int(lv)
    row[2] = int(slv)
    row[6] = hp
    row[7] = hp
    return row


def _exploration_units(entries, side):
    """Battle units for the single-lane exploration map.

    GameMapManager.getExplorationData() builds GameMapData.line = 1, but
    _pvp_units spreads units over lines 0..2; formatAttrs() would then call
    getLineSpr(1/2) on a one-lane map and crash.  Pin everything to line 0.

    `pos` must use the same 0..LINE_POS(3000) scale as _pvp_units: the client
    does side1 x = 1 - pos/LINE_POS and side2 x = pos/LINE_POS.  Using a
    0..1000 scale here put our team on the right and the enemies on the left
    (the "enemy standing on the wrong side" bug).
    """
    units = _pvp_units(entries, side)
    # pos is the depth along the lane (posToPixel -> y).  PVE uses 0..0.35
    # for the player team and 0.6..0.9 for the enemy team; mirror that here
    # so our team stands at the front/bottom and the enemies at the far/top
    # instead of both teams overlapping around the middle.
    base = 0.10 if side == 1 else 0.70
    for i, unit in enumerate(units):
        unit["line"] = 0
        unit["pos"] = int((base + 0.08 * i) * 3000)
    return units


def _exploration_enemy(stage):
    lv = min(80, 18 + max(1, int(stage)) * 2)
    team = [("A_2003_2", lv), ("A_2002_4", lv), ("A_2005_4", lv)]
    rows = [_exploration_row(aid, l) for (aid, l) in team]
    power = int(sum(_avatar_power(aid, l) for (aid, l) in team))
    return {"team": team, "rows": rows, "lv": lv, "power": power}


def _pvp_my_units(acc, side=1):
    team = _ensure_team(acc)[0]
    avatars = _ensure_avatars(acc)
    entries = []
    metas = []
    for key in team:
        if not key:
            continue
        av = avatars.get(key)
        if not av:
            continue
        entries.append((key.split("|")[0], int(av.get("lv", 1))))
        metas.append(av)
        if len(entries) >= 5:
            break
    units = _pvp_units(entries, side)
    # Carry the account hero's limit-break/phase so the arena battle card
    # keeps its golden 6★ limit-break frame (client reads data.limit_break).
    for unit, av in zip(units, metas):
        unit["limit_break"] = int(av.get("limit_break", 0) or 0)
        unit["phase"] = int(av.get("phase", 0) or 0)
        unit["morph"] = int(av.get("morph", 0) or 0)
        unit["slv"] = int(av.get("slv", 1) or 1)
    return units


def empty_combat_score():
    return {"normal": {}, "hard": {}, "ploy": {}, "guild": {}}


SUMMONER_MAX_LV = 60


def max_exp_for(lv):
    # exp_config = [0, 100, 0, 60] -> 100 * lv; no further exp at 60
    return 100 * lv if lv < SUMMONER_MAX_LV else 0


def grant_exp(acc, amount):
    """Add exp and apply level-ups using the same formula as getCurrLvMaxEXP."""
    lv = int(acc.get("lv", 25))
    exp = int(acc.get("exp", 0)) + int(amount)
    while lv < SUMMONER_MAX_LV:
        need = max_exp_for(lv)
        if need <= 0 or exp < need:
            break
        exp -= need
        lv += 1
    if lv >= SUMMONER_MAX_LV:
        exp = 0
    acc["lv"] = lv
    acc["exp"] = exp
    return lv, exp


def mark_stage_stars(acc, cid, stars=3, diff=0):
    """Record the star count in the structure ItemPVEcombat reads:
    user.combat_score.normal["M_001"] = [flag, [stage1Stars, stage2Stars, ...]]
    """
    parts = cid.split("_")
    if len(parts) != 3:
        return
    chapter, idx = parts[0] + "_" + parts[1], int(parts[2])
    cs = acc.setdefault("combat_score", empty_combat_score())
    if int(diff) == 2:
        tab = "ploy"
    elif int(diff) == 1:
        tab = "hard"
    else:
        tab = "normal"
    normal = cs.setdefault(tab, {})
    entry = normal.get(chapter)
    if not isinstance(entry, list) or len(entry) < 2:
        entry = ["0", []]
    star_list = entry[1]
    while len(star_list) < idx:
        star_list.append(0)
    star_list[idx - 1] = max(int(star_list[idx - 1] or 0), stars)
    normal[chapter] = [entry[0], star_list]


def next_stage(cid):
    """Return the stage the client should consider 'current' after clearing cid."""
    try:
        i = PVE_STAGE_ORDER.index(cid)
    except ValueError:
        return PVE_STAGE_ORDER[0]
    if i + 1 < len(PVE_STAGE_ORDER):
        return PVE_STAGE_ORDER[i + 1]
    return cid                      # chapter finished: stay on the last stage


def _energy_max(acc):
    ec = _cfg()["system_simple"]["energy_config"]
    return min(int(ec[0]) + int(acc.get("lv", 25)) * int(ec[1]), int(ec[3]))


def _energy_now(acc, now_ms=None):
    """Current PVE stamina, mirroring GlobalFunction.getEnergy()."""
    ec = _cfg()["system_simple"]["energy_config"]
    max_e = _energy_max(acc)
    if now_ms is None:
        now_ms = _now_ms()
    try:
        last = int(acc.get("energy", 0) or 0)
    except (TypeError, ValueError):
        last = 0
    if not last:
        return max_e
    regen_ms = int(ec[2]) * 60 * 1000
    if regen_ms <= 0:
        return max_e
    cur = int(max(0, now_ms - last) / regen_ms)
    return min(cur, max_e)


def _energy_stamp(value, now_ms=None):
    """Timestamp that makes the client compute `value` current stamina."""
    ec = _cfg()["system_simple"]["energy_config"]
    if now_ms is None:
        now_ms = _now_ms()
    return now_ms - int(value) * int(ec[2]) * 60 * 1000


def _frag_energy_max(acc):
    cc = _cfg()["system_simple"]["capacity_config"]
    return int(cc[0])


def _frag_energy_now(acc, now_ms=None):
    cc = _cfg()["system_simple"]["capacity_config"]
    max_e = int(cc[0])
    if now_ms is None:
        now_ms = _now_ms()
    try:
        last = int(acc.get("fragment_energy", 0) or 0)
    except (TypeError, ValueError):
        last = 0
    if not last:
        return max_e
    regen_ms = int(cc[1]) * 60 * 1000
    if regen_ms <= 0:
        return max_e
    return min(int(max(0, now_ms - last) / regen_ms), max_e)


def _frag_energy_stamp(value, now_ms=None):
    cc = _cfg()["system_simple"]["capacity_config"]
    if now_ms is None:
        now_ms = _now_ms()
    return now_ms - int(value) * int(cc[1]) * 60 * 1000


def _energy_full_since():
    """A timestamp old enough that energy regen has filled the bar.

    The client derives current energy as (now - this) / regen_minutes, capped
    by the config maximum (100 * 5 min = 30000 s), so 10 hours is safely full.
    """
    return datetime.datetime.utcnow() - datetime.timedelta(hours=10)


def _bot_helper(uid, name, aid="A_1012_4", lv=25):
    """One entry for PanelPVEfriend's online-user list.

    ``uid`` must contain "bot": GlobalFunction.check_bot_user() then skips the
    "used today" cooldown and shows the helper on final-stage fights.
    """
    return {
        "uid": uid,
        "name": name,
        "lv": lv,
        "vip_lv": 0,
        "current_rank": 99999,
        "login_time": datetime.datetime.utcnow(),
        # ItemPVEfriend.init() copies avatar.aid into avatar.id, then builds
        # an Avatar from it; the same fields as make_user()'s avatars work.
        "avatar": {
            "aid": aid, "lv": lv, "exp": 0, "slv": 1, "star": 4,
            "love": 0, "phase": 0, "morph": 0, "love_exp": 0,
            "tpl": [1, 1, 1, 400, 3000],
            "hp_max": 5000, "hp": 5000, "ap": 500,
            "de_ph": 100, "de_ma": 100,
        },
    }


_CFG_CACHE = None


def _cfg():
    """default_cfg() is static; build it once for avatar math helpers."""
    global _CFG_CACHE
    if _CFG_CACHE is None:
        _CFG_CACHE = default_cfg()
    return _CFG_CACHE


def _avatar_star(aid):
    try:
        return int(aid.split("_")[2])
    except (IndexError, ValueError):
        return 1


def _family_catalog_stars(fam):
    """All star tiers the catalog still offers for one avatar family."""
    prefix = fam + "_"
    out = []
    for aid in AVATAR_CATALOG:
        if aid.startswith(prefix):
            try:
                out.append(int(aid.rsplit("_", 1)[1]))
            except ValueError:
                continue
    return out


def _is_low_star_tier(aid):
    """True for a synthetic avatar tier the client has no icon for.

    Hero families only ship icons from some star upward (e.g. A_1033 伊芙琳
    has 5★/6★ only).  The catalog used to invent tiers 2..top using the
    nearest icon, which made a 2★ card display the 5★ purple art.  Such
    tiers are no longer in the catalog; this helper identifies the stale
    copies so the account migration can drop them.
    """
    if not isinstance(aid, str) or aid in AVATAR_CATALOG:
        return False
    if "_" not in aid:
        return False
    fam, _, star = aid.rpartition("_")
    try:
        star = int(star)
    except ValueError:
        return False
    stars = _family_catalog_stars(fam)
    return bool(stars) and star < min(stars)


def _low_star_clamp(aid):
    """Raise a below-icon avatar id to its family's lowest real star."""
    if not _is_low_star_tier(aid):
        return aid
    fam, _, star = aid.rpartition("_")
    stars = _family_catalog_stars(fam)
    try:
        star = int(star)
    except ValueError:
        star = min(stars)
    return "%s_%d" % (fam, min(stars, key=lambda s: (abs(s - star), s)))


def _avatar_tpl(aid):
    """[signType, actionType, damageType, speed, range] for Avatar.init()."""
    av = _cfg()["avatar"].get(aid)
    if av:
        tl, pl = av["tl"], av["pl"]
        return [tl[0], tl[1], tl[2], pl[8], pl[9]]
    return [1, 1, 1, 300, 250]


def _make_avatar(aid, lv=1, exp=0):
    """One avatar instance for user.avatars.

    Stats are deliberately NOT sent as ``hp_max``: Avatar.initFightAttr()
    then computes HP/attack/defense from cfg.avatar (hp0 + hp1*lv …), so
    feeding materials and leveling up actually raises combat power.  The
    hp/ap/de_ph/de_ma fields are percent bonuses (0 by default); the client
    multiplies them by Avatar.PITH_POINT (culture.culture_pith).
    """
    # Never hand out a star tier the client has no art for.
    aid = _low_star_clamp(aid)
    star = _avatar_star(aid)
    return {
        # 2026-10-22: every newly obtained hero starts with normal-skill
        # level 1.  Skill levels only grow by swallowing skill books /
        # cookies; star level must not hand out free levels.
        "lv": int(lv), "exp": int(exp),
        "slv": 1,
        "star": star, "love": 0, "phase": 0, "morph": 0,
        "limit_break": 0,
        "love_exp": 0, "tpl": _avatar_tpl(aid),
        "hp": 0, "ap": 0, "de_ph": 0, "de_ma": 0,
    }


_DRAW_POOL = None
# Gold/score altar: 2-6★ heroes only.  7★ is progression-only (star-up) and
# must never appear in a draw.
_DRAW_WEIGHTS = {2: 100, 3: 60, 4: 25, 5: 8, 6: 2}
# VIP altar: no 2★ cards, noticeably better star odds.
_VIP_DRAW_WEIGHTS = {3: 50, 4: 30, 5: 14, 6: 6}


def _build_draw_pool(weights):
    pool = []
    for aid, meta in AVATAR_CATALOG.items():
        if int(meta.get("kind", 1) or 0) != 1:
            continue
        try:
            star = int(meta.get("star", 2))
        except (TypeError, ValueError):
            continue
        weight = int(weights.get(star, 0) or 0)
        if star < 2 or star > 6 or weight <= 0:
            continue
        pool.append((aid, weight))
    return pool


def _draw_pool(weights=None):
    """Weighted altar pool: story heroes only, rarer stars are rarer."""
    global _DRAW_POOL
    if weights is not None:
        return _build_draw_pool(weights)
    if _DRAW_POOL is None:
        _DRAW_POOL = _build_draw_pool(_DRAW_WEIGHTS)
    return _DRAW_POOL


def _draw_one(weights=None):
    pool = _draw_pool(weights)
    if not pool:
        return None
    total = sum(w for _aid, w in pool)
    roll = random.uniform(0, total)
    upto = 0.0
    for aid, weight in pool:
        upto += weight
        if roll <= upto:
            return aid
    return pool[-1][0]


def _draw_min_star(drawn, min_star):
    """Ten-draw guarantee: replace the last card if all are below min_star."""
    if not drawn:
        return drawn
    if all(_avatar_star(aid) >= min_star for aid in drawn):
        return drawn
    candidates = [aid for aid, meta in AVATAR_CATALOG.items()
                  if int(meta.get("kind", 1) or 0) == 1
                  and int(meta.get("star", 0) or 0) == min_star]
    if candidates:
        drawn[-1] = random.choice(candidates)
    return drawn


# ---------------------------------------------------------------------------
# 2026-10-21 altar pools, rebuilt from the user's gallery-position tables.
# Positions are 1-based ranks of the 256 gallery tiles:
#   1-141 heroes, 142-213 monsters, 214-224 buildings, 225-256 materials.
# ---------------------------------------------------------------------------
# Gold altar side products: positions 193-213, excluding 201/202/211.
_GOLD_SIDE_IDS = [
    "A_3001_2", "A_3002_2", "A_3003_3", "A_3004_3",
    "A_3005_4", "A_3006_4", "A_3007_5", "A_3008_5",
    "A_4001_3", "A_4004_4", "A_4005_5", "A_4006_5",
    "A_4007_5", "A_4008_5", "A_4012_4", "A_4014_5",
    "A_4016_5", "A_4018_5",
]
# Ticket/VIP side products: 145-150, 165-192, 252-255.
_TICKET_SIDE_IDS = [
    "A_2004_4", "A_2005_4", "A_2006_5", "A_2008_5",
    "A_2009_5", "A_2010_5",
    "A_2108_5",
    "A_2300_4", "A_2301_5", "A_2302_5", "A_2303_5",
    "A_2304_5", "A_2305_5", "A_2306_5", "A_2307_5",
    "A_2308_5", "A_2309_5", "A_2310_5", "A_2311_5",
    "A_2312_5", "A_2313_5", "A_2314_5", "A_2315_5",
    "A_2316_5", "A_2317_5", "A_2318_5", "A_2319_5",
    "A_2320_5", "A_2321_5", "A_2322_5", "A_2323_5",
    "A_2324_5", "A_2325_5", "A_2326_5",
    "A_6995_5", "A_6996_5", "A_6997_5", "A_6998_5",
]
# Position 164 = 技能餅乾-小.
_TICKET_COOKIE_IDS = ["A_2107_4"]
_MATERIAL_252_255 = ["A_6995_5", "A_6996_5", "A_6997_5", "A_6998_5"]
_MAT_249 = "A_6992_6"          # 技能餅乾-大
_MAT_250 = "A_6993_6"          # 魔法藥水
_MAT_251 = "A_6994_6"          # 渡厄
# 2026-10-24 VIP altar UP rotation: 7 heroes, 48-hour cycles, refreshed at
# the real system clock's 04:00.  Anchor = 2026-10-24 04:00 local, so the
# first cycle is 莫德凱撒 and the next switch is 2026-10-26 04:00.
_UP_ROTATION = ["A_1137", "A_1310", "A_1216", "A_1079",
                "A_1099", "A_1209", "A_1036"]
_UP_ANCHOR = datetime.datetime(2026, 10, 24, 4, 0, 0)
_UP_PERIOD_HOURS = 48
_UP_FAMILY = _UP_ROTATION[0]
_UP5 = _UP_FAMILY + "_5"
_UP6 = _UP_FAMILY + "_6"
_UP_END = _UP_ANCHOR + datetime.timedelta(hours=_UP_PERIOD_HOURS)

_ALTAR_POOLS = None


def _up_rotation_state(now=None):
    """Return (current_up_family, next_switch_datetime)."""
    now = now or datetime.datetime.now()
    period = datetime.timedelta(hours=_UP_PERIOD_HOURS)
    elapsed = (now - _UP_ANCHOR).total_seconds()
    idx = int(elapsed // period.total_seconds())
    fam = _UP_ROTATION[idx % len(_UP_ROTATION)]
    end = _UP_ANCHOR + period * (idx + 1)
    return fam, end


def _refresh_up_rotation():
    """Apply the current 48h UP hero; rebuild lottery pools when it changes."""
    global _UP_FAMILY, _UP5, _UP6, _UP_END, _ALTAR_POOLS
    fam, end = _up_rotation_state()
    if fam != _UP_FAMILY:
        _UP_FAMILY = fam
        _UP5 = fam + "_5"
        _UP6 = fam + "_6"
        _ALTAR_POOLS = None
    _UP_END = end
    return fam, end


def _valid_aids(ids):
    return [aid for aid in ids if aid in AVATAR_CATALOG]


def _novice_bases():
    """Gallery 1-21 and 127-134 (novice-tier draw pool)."""
    ranks = _gallery_display_ranks()
    return [ranks[pos] for pos in list(range(1, 22)) + list(range(127, 135))
            if pos in ranks]


# User's gallery-position list for the advanced tier.  HERO_INDEX follows the
# HERO_NAMES insertion order, which places the A_12xx skin cards at 104-112;
# the real gallery sorts by tl[9] and puts them at 201+, so using HERO_INDEX
# here pulled high-tier heroes into the 點券祭壇.  Resolve positions against
# the actual tl[9] gallery ranking instead.
_ADVANCED_GALLERY_POSITIONS = (
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
    37, 39, 40, 41, 42, 49, 51, 52, 53,
    57, 59, 60, 62, 67, 68, 75,
)
def _advanced_bases():
    tier_map = _gallery_tier_map()
    return [base for base, tier in tier_map.items() if tier == "advanced"]


def _star_aids(bases, stars):
    out = []
    for base in bases:
        for star in stars:
            aid = "%s_%d" % (base, star)
            if aid in AVATAR_CATALOG:
                out.append(aid)
    return out


def _altar_pools():
    """Lazily build every pool used by the three altars."""
    global _ALTAR_POOLS
    _refresh_up_rotation()
    if _ALTAR_POOLS is not None:
        return _ALTAR_POOLS
    novice = _novice_bases()
    advanced = _advanced_bases()
    adv_no_up = [b for b in advanced if b != _UP_FAMILY]
    _ALTAR_POOLS = {
        "gold_side": _valid_aids(_GOLD_SIDE_IDS),
        "gold_low": _star_aids(novice, (2, 3, 4)),
        "gold_five": _star_aids(novice, (5,)),
        "gold_mat": _valid_aids(_MATERIAL_252_255),
        "ticket_side": _valid_aids(_TICKET_SIDE_IDS),
        "ticket_cookie": _valid_aids(_TICKET_COOKIE_IDS),
        "ticket_low": _star_aids(advanced, (2, 3, 4)),
        "ticket_five": _star_aids(advanced, (5,)),
        "ticket_six": _star_aids(advanced, (6,)),
        "vip_side": _valid_aids(_TICKET_SIDE_IDS),
        "vip_cookie": _valid_aids(_TICKET_COOKIE_IDS),
        "vip_low": _star_aids(advanced, (2, 3, 4)),
        "vip_five": _star_aids(adv_no_up, (5,)),
        "vip_six": _star_aids(adv_no_up, (6,)),
        "vip_up5": _valid_aids([_UP5]),
        "vip_up6": _valid_aids([_UP6]),
        "mat249": _valid_aids([_MAT_249]),
        "mat250": _valid_aids([_MAT_250]),
        "mat251": _valid_aids([_MAT_251]),
        # 2026-10-25: 神眷秘寶 added to the VIP altar at 2%.
        "vip_6999": _valid_aids(["A_6999_5"]),
    }
    return _ALTAR_POOLS


def _pick_pool(pairs):
    """Pick a category by weight, then a uniform item from its pool."""
    pairs = [(pool, weight) for pool, weight in pairs if pool]
    if not pairs:
        return None
    total = sum(weight for _pool, weight in pairs)
    roll = random.uniform(0, total)
    upto = 0.0
    for pool, weight in pairs:
        upto += weight
        if roll <= upto:
            return random.choice(pool)
    return random.choice(pairs[-1][0])


def _draw_gold():
    p = _altar_pools()
    return _pick_pool([
        (p["gold_side"], 50),
        (p["gold_low"], 20),
        (p["gold_mat"], 24),
        (p["gold_five"], 6),
    ])


def _draw_ticket():
    p = _altar_pools()
    return _pick_pool([
        (p["ticket_side"], 40),
        (p["ticket_cookie"], 10),
        (p["ticket_low"], 43),
        (p["ticket_five"], 6),
        (p["ticket_six"], 1),
    ])


def _vip_six_chance(misses):
    """6★ chance after ``misses`` consecutive non-6★ draws.

    1% for draws 1-34; from the 34th consecutive draw onwards +6% per draw,
    as requested: 7%, 13%, 19% ... capped at 100%.
    """
    if misses < 33:
        return 0.01
    return min(1.0, 0.01 + 0.06 * (misses - 32))


def _pick_vip_six(up_next):
    p = _altar_pools()
    up, adv = p["vip_up6"], p["vip_six"]
    if up_next and up:
        return up[0]
    if up and adv:
        return up[0] if random.random() < 0.5 else random.choice(adv)
    if up:
        return up[0]
    return random.choice(adv) if adv else None


def _pick_vip_five_guarantee():
    p = _altar_pools()
    up, adv = p["vip_up5"], p["vip_five"]
    if up and adv:
        return up[0] if random.random() < 0.5 else random.choice(adv)
    if up:
        return up[0]
    return random.choice(adv) if adv else None


def _hero_card_star(aid):
    """Star of a drawn *hero* card, or 0 for monsters/materials.

    Side products and 249/250/251 materials can themselves be 5★/6★ cards;
    they must not satisfy hero pity counters or the 6★ UP reset.
    """
    meta = AVATAR_CATALOG.get(aid) or {}
    if int(meta.get("kind", 1) or 0) != 1:
        return 0
    return _avatar_star(aid)


def _draw_vip_normal(misses, up_next):
    """One VIP draw; returns (aid, natural_six_star)."""
    p = _altar_pools()
    if random.random() < _vip_six_chance(misses):
        return _pick_vip_six(up_next), True
    return _pick_pool([
        # 2026-10-25: exp materials 40% -> 38%, 神眷秘寶 A_6999_5 2%.
        (p["vip_side"], 38),
        (p["vip_cookie"], 10),
        (p["vip_low"], 37),
        (p["vip_five"], 2),
        (p["vip_up5"], 4),
        (p["mat251"], 1),
        (p["mat249"], 2.5),
        (p["mat250"], 2.5),
        (p["vip_6999"], 2),
    ]), False


def _altar_draw_gold(times):
    p = _altar_pools()
    drawn = [_draw_gold() for _ in range(times)]
    # Every ten-pull guarantees one five-star novice from the 5★ families
    # (1-21 + A_1903..A_1906).
    if times == 10 and p["gold_five"]:
        five = set(p["gold_five"])
        if not any(aid in five for aid in drawn):
            drawn[-1] = random.choice(p["gold_five"])
    return drawn


def _altar_draw_ticket(acc, times):
    """Points altar with cumulative 10-draw 5★ / 50-draw 6★ pity."""
    p = _altar_pools()
    c10 = int(acc.get("ticket_10_count", 0) or 0)
    f5 = bool(acc.get("ticket_10_five", 0))
    c50 = int(acc.get("ticket_50_count", 0) or 0)
    drawn = []
    for _ in range(times):
        c10 += 1
        c50 += 1
        aid = _draw_ticket()
        star = _hero_card_star(aid)
        # 50-draw 6★ pity: force the last draw if 50 non-6★ heroes in a row.
        if c50 >= 50 and star < 6 and p["ticket_six"]:
            aid = random.choice(p["ticket_six"])
            star = 6
        # 10-draw 5★ pity: only if this cycle has not produced a 5★ hero.
        if c10 >= 10:
            if not f5 and star < 5 and p["ticket_five"]:
                aid = random.choice(p["ticket_five"])
                star = 5
            c10 = 0
            f5 = False
        elif star >= 5:
            f5 = True
        if star >= 6:
            c50 = 0
        drawn.append(aid)
    acc["ticket_10_count"] = c10
    acc["ticket_10_five"] = 1 if f5 else 0
    acc["ticket_50_count"] = c50
    return drawn


def _altar_draw_vip(acc, times):
    """VIP altar: dynamic 6★ pity, 10-draw 5★+249/250, UP guarantee."""
    p = _altar_pools()
    mats = set(p["mat249"]) | set(p["mat250"])
    c10 = int(acc.get("vip_10_count", 0) or 0)
    f5 = bool(acc.get("vip_10_five", 0))
    fmat = bool(acc.get("vip_10_mat", 0))
    misses = int(acc.get("vip_6_misses", 0) or 0)
    up_next = bool(acc.get("vip_up_next", 0))
    drawn = []
    for _ in range(times):
        c10 += 1
        aid, _natural6 = _draw_vip_normal(misses, up_next)
        star = _hero_card_star(aid)
        if c10 >= 10:
            # Guaranteed 5★ hero: 50% UP / 50% advanced.
            if not f5 and star < 5:
                aid = _pick_vip_five_guarantee()
                star = _hero_card_star(aid)
            drawn.append(aid)
            # Guaranteed 249/250 as an extra card, 50/50.  If this 10th
            # draw is itself a 249/250, it already satisfies the guarantee.
            if not fmat and aid not in mats:
                drawn.append(random.choice([_MAT_249, _MAT_250]))
            c10 = 0
            f5 = False
            fmat = False
        else:
            drawn.append(aid)
            if star >= 5:
                f5 = True
            if aid in mats:
                fmat = True
        # 6★ pity resets on any 6★; UP flag forces the next 6★ to UP.
        if star >= 6:
            misses = 0
            up_next = (aid != _UP6)
        else:
            misses += 1
    acc["vip_10_count"] = c10
    acc["vip_10_five"] = 1 if f5 else 0
    acc["vip_10_mat"] = 1 if fmat else 0
    acc["vip_6_misses"] = misses
    acc["vip_up_next"] = 1 if up_next else 0
    return drawn


def _starter_avatars(lv=1):
    return {
        "A_1001_2|0": _make_avatar("A_1001_2", lv),
        "A_1012_4|1": _make_avatar("A_1012_4", lv),
        "A_1013_3|2": _make_avatar("A_1013_3", lv),
    }


def _ensure_avatars(acc):
    """Create/migrate the persistent avatar inventory in an account.

    Older saves only had progress; seed the heroes at a small level based on
    how far the account has already advanced, so existing progress does not
    suddenly become unwinnable.  From here on levels only come from feeding
    materials through user.swallow_avatar.
    """
    avatars = acc.get("avatars")
    if not isinstance(avatars, dict) or not avatars:
        cleared = sum(1 for v in (acc.get("cleared") or {}).values()
                      if int(v or 0) > 0)
        lv = max(1, min(10, 1 + cleared // 2))
        acc["avatars"] = _starter_avatars(lv)
        acc.setdefault("next_slot", 100)
    else:
        acc.setdefault("next_slot", 100 + len(avatars))
    # 2026-10-22: newly obtained heroes start at normal-skill level 1; the
    # skill only grows by swallowing skill books/cookies.  The old rule
    # auto-raised slv to star-1, so a fresh 6★ card showed 英雄技LV5 (and a
    # 6★→7★ star-up carried that level over).  Drop the untouched auto
    # values once.  Only level-1 cards are reset, and any level above the
    # old auto value was earned with skill materials, so it is kept.
    reset_slv = not acc.get("slv_fresh_v1")
    for key, av in acc["avatars"].items():
        if not isinstance(av, dict):
            continue
        av.setdefault("limit_break", 0)
        av.setdefault("slv", 1)
        if not reset_slv:
            continue
        try:
            auto = min(10, max(1, _avatar_star(key.split("|")[0]) - 1))
            cur = int(av.get("slv", 1) or 1)
            lv = int(av.get("lv", 1) or 1)
        except (TypeError, ValueError, IndexError):
            continue
        if lv <= 1 and 1 < cur <= auto:
            av["slv"] = 1
    if reset_slv:
        acc["slv_fresh_v1"] = 1
    # 2026-10-25: 5★ phases no longer grant pith (star-order fix: 5★满阶 must
    # stay below 6★0阶).  Clear the old 25/阶 values once on existing cards.
    if not acc.get("phase_pith_zero_v1"):
        for _key, _av in acc["avatars"].items():
            if not isinstance(_av, dict):
                continue
            try:
                _star = _avatar_star(_key.split("|")[0])
            except (AttributeError, IndexError):
                continue
            if _star == 5:
                for _fld in ("hp", "ap", "de_ph", "de_ma"):
                    _av[_fld] = 0
        acc["phase_pith_zero_v1"] = 1
    # A_2001_* is the old internal EXP material.  It is hidden from the
    # gallery, its icon renders as a blank circle and opening its detail
    # panel crashes the client.  Migrate any leftovers to the visible
    # 武鬥密卷-中 card.
    stale = [k for k in acc["avatars"]
             if isinstance(k, str) and k.startswith("A_2001_")]
    if stale:
        slot = int(acc.get("next_slot", 100))
        for old in stale:
            new_key = "A_6996_4|%d" % slot
            slot += 1
            acc["avatars"][new_key] = _new_avatar_instance("A_6996_4")
            del acc["avatars"][old]
        acc["next_slot"] = slot
    # 2026-10-23: hero families only ship icons from some star upward
    # (A_1033 伊芙琳 has 5★/6★ only).  The catalog no longer invents tiers
    # below the lowest real icon, so drop the stale synthetic copies once.
    # Their team / DN / expedition references fall back to the best owned
    # valid copy of the same family, and old mail gifts are clamped too.
    if not acc.get("low_star_art_v1"):
        av_cfg_now = _cfg()["avatar"]
        fam_pick = {}
        for k in acc["avatars"]:
            aid = k.split("|")[0]
            if aid not in av_cfg_now:
                continue
            fam = aid.rsplit("_", 1)[0]
            try:
                star = int(aid.rsplit("_", 1)[1])
            except ValueError:
                continue
            cur = fam_pick.get(fam)
            if cur is None or star > cur[0]:
                fam_pick[fam] = (star, k)
        bad = {}
        for k in list(acc["avatars"]):
            aid = k.split("|")[0]
            if _is_low_star_tier(aid):
                pick = fam_pick.get(aid.rsplit("_", 1)[0])
                bad[k] = pick[1] if pick else None
        if bad:
            for row in acc.get("team") or []:
                if isinstance(row, list):
                    for i, v in enumerate(row):
                        if v in bad:
                            row[i] = bad[v]
            for node in (acc.get("dn") or {}).values():
                if isinstance(node, list):
                    for i, v in enumerate(node):
                        if v in bad:
                            node[i] = bad[v]
            exp_state = acc.get("expedition_state") or {}
            aids = exp_state.get("aids")
            if isinstance(aids, list):
                new_aids = []
                for v in aids:
                    repl = bad.get(v, v)
                    if repl:
                        new_aids.append(repl)
                exp_state["aids"] = new_aids
            for k in bad:
                del acc["avatars"][k]
        for msg in (acc.get("gift_msgs") or {}).values():
            gd = msg.get("gift_dict") if isinstance(msg, dict) else None
            av_gift = gd.get("avatar") if isinstance(gd, dict) else None
            if not isinstance(av_gift, dict):
                continue
            fixed = {}
            for aid_key, cnt in av_gift.items():
                if isinstance(cnt, dict):
                    fixed[aid_key] = cnt
                    continue
                new_aid = _low_star_clamp(str(aid_key).split("|")[0])
                if isinstance(cnt, int) and isinstance(fixed.get(new_aid), int):
                    fixed[new_aid] += cnt
                elif new_aid not in fixed:
                    fixed[new_aid] = cnt
            gd["avatar"] = fixed
        acc["low_star_art_v1"] = 1
    # 英雄戰魂 (avatar_soul) is keyed by avatar id as well; PanelCenterSouls
    # builds an Avatar for each soul icon, so a removed tier would throw
    # #1009 on the lobby screen.  Clamp the keys once.
    if not acc.get("low_star_soul_v1"):
        souls = acc.get("avatar_soul")
        if isinstance(souls, dict):
            soul_cfg = _cfg()["avatar"]
            fixed = {}
            for aid, cnt in souls.items():
                new_aid = _low_star_clamp(str(aid))
                if new_aid not in soul_cfg:
                    continue
                if isinstance(cnt, int) and isinstance(fixed.get(new_aid), int):
                    fixed[new_aid] += cnt
                elif new_aid not in fixed:
                    fixed[new_aid] = cnt
            acc["avatar_soul"] = fixed
        acc["low_star_soul_v1"] = 1
    # Any avatar whose template is absent from cfg.avatar makes the client's
    # Avatar.initSkills() throw #1009 and breaks the whole barracks list
    # (e.g. old PVE drops of A_6995_4, a tier that does not exist).  Move
    # such instances to the nearest existing star of the same family.
    av_cfg = _cfg()["avatar"]
    broken = [k for k in acc["avatars"]
              if isinstance(k, str) and k.split("|")[0] not in av_cfg]
    if broken:
        slot = int(acc.get("next_slot", 100))
        for old in broken:
            aid = old.split("|")[0]
            parts = aid.split("_")
            fam = "_".join(parts[:2])
            try:
                star = int(parts[2])
            except (IndexError, ValueError):
                star = 1
            cands = [k for k in av_cfg if k.startswith(fam + "_")]
            if cands:
                cands.sort(key=lambda k: abs(
                    int(k.split("_")[2]) - star))
                new_aid = cands[0]
            else:
                new_aid = "A_6996_4"
            new_key = "%s|%d" % (new_aid, slot)
            slot += 1
            inst = acc["avatars"][old]
            acc["avatars"][new_key] = inst
            del acc["avatars"][old]
            for row in acc.get("team") or []:
                if isinstance(row, list):
                    for i, v in enumerate(row):
                        if v == old:
                            row[i] = new_key
        acc["next_slot"] = slot
    # 2026-10-23: avatar keys are "<aid>|<slot>" and the client resolves a
    # battle avatar by the slot number alone (Avatar.getUserAvatarObj).  Two
    # cards sharing one slot therefore make the battle use the WRONG card
    # (this is how 費德提克 once resolved to a 神眷秘寶 material, showing him
    # as un-limit-broken).  Re-key any duplicate slot and keep next_slot
    # above every existing slot.
    avatars_now = acc["avatars"]
    refs = set()
    for row in acc.get("team") or []:
        if isinstance(row, list):
            refs.update(v for v in row if isinstance(v, str))
    exp_state = acc.get("expedition_state") or {}
    if isinstance(exp_state.get("aids"), list):
        refs.update(v for v in exp_state["aids"] if isinstance(v, str))
    for node in (acc.get("dn") or {}).values():
        if isinstance(node, list):
            refs.update(v for v in node if isinstance(v, str))
    slot_owner = {}
    max_slot = 0
    for k in list(avatars_now):
        if not isinstance(k, str) or "|" not in k:
            continue
        try:
            slot = int(k.split("|")[1])
        except ValueError:
            continue
        max_slot = max(max_slot, slot)
        prev = slot_owner.get(slot)
        if prev is None:
            slot_owner[slot] = k
            continue
        # Prefer the referenced card; when neither is referenced keep the
        # older instance (dict insertion order) and re-key the newer one.
        keep = prev if (prev in refs or k not in refs) else k
        move = k if keep == prev else prev
        slot_owner[slot] = keep
        try:
            next_slot = max(int(acc.get("next_slot", 100)), max_slot + 1)
        except (TypeError, ValueError):
            next_slot = max_slot + 1
        new_key = "%s|%d" % (move.split("|")[0], next_slot)
        max_slot = next_slot
        avatars_now[new_key] = avatars_now.pop(move)
        for row in acc.get("team") or []:
            if isinstance(row, list):
                for i, v in enumerate(row):
                    if v == move:
                        row[i] = new_key
        acc["next_slot"] = next_slot + 1
        slot_owner[next_slot] = new_key
    try:
        if int(acc.get("next_slot", 100)) <= max_slot:
            acc["next_slot"] = max_slot + 1
    except (TypeError, ValueError):
        acc["next_slot"] = max_slot + 1
    return acc["avatars"]


def _ensure_team(acc):
    """Persistent five-slot team; star-up changes keys, so it must be saved."""
    avatars = _ensure_avatars(acc)
    team = acc.get("team")
    if not (isinstance(team, list) and team and isinstance(team[0], list)):
        keys = [k for k in ("A_1001_2|0", "A_1012_4|1", "A_1013_3|2")
                if k in avatars]
        team = [keys + [None] * (5 - len(keys))]
        acc["team"] = team
    else:
        row = [k if isinstance(k, str) and k in avatars else None
               for k in team[0][:5]]
        while len(row) < 5:
            row.append(None)
        if not any(row):
            keys = [k for k in ("A_1001_2|0", "A_1012_4|1", "A_1013_3|2")
                    if k in avatars]
            row[:len(keys)] = keys
        team[0] = row
    # 2026-10-23: same-hero team restriction (one card per hero family).
    for _row in acc.get("team") or []:
        if isinstance(_row, list):
            _dedupe_team_row(_row)
    return team


def _final_equip_eid(eid):
    """Unified endgame equipment template.

    Non-book gear -> 6★ orange; E_6 skill books -> 7★ red.  The helper is
    deliberately idempotent and works for five-digit alias ids too.  It is
    applied when new equipment is created so low-star drops never re-enter
    the inventory after the 2026-10-21 cleanup.
    """
    if not isinstance(eid, str):
        return eid
    parts = eid.split("_")
    if len(parts) != 3 or not parts[1]:
        return eid
    target = 7 if parts[1][0] == "6" else 6
    cand = "%s_%s_%d" % (parts[0], parts[1], target)
    return cand if cand in EQUIP_CATALOG else eid


def _fixed_equip_attrs(eid):
    """Max-level affix map for one equipment template (2026-10-21).

    The client scales these linearly with equipment level; at level 150 they
    are exactly the configured max values.  crit/tough stay in 0.1% units;
    critdmg is a percent bonus on top of the 175% base.
    """
    return _endgame_affix_max(eid)


def _ensure_equips(acc):
    """Persistent equipment inventory + per-team-set worn ids.

    user.my_equips: instance id -> {eid, lv, slv, ...}
    user.as_equips: 5 team sets x 6 slots of instance ids (Equip.setEquips()
                    reads as_equips[teamSlot]).
    """
    my = acc.get("my_equips")
    if not isinstance(my, dict):
        my = {}
        acc["my_equips"] = my
    # Older saves stored five-digit icon ids (E_1001_10000).  Equip.getStar()
    # parses the last id segment, so migrate them to the short star form
    # (E_1001_1) that star tables and the soul exchange expect.
    for inst in my.values():
        eid = inst.get("eid") if isinstance(inst, dict) else None
        if not isinstance(eid, str):
            continue
        parts = eid.split("_")
        if len(parts) == 3 and len(parts[2]) == 5 and parts[2].isdigit():
            short = "E_%s_%d" % (parts[1], int(parts[2]) // 10000)
            if short in EQUIP_CATALOG:
                inst["eid"] = short
    # 2026-10-21 endgame cleanup, applied idempotently on every equipment
    # access:
    #   * delete every 4★-and-below item;
    #   * turn surviving non-book gear into 6★ (orange frame);
    #   * turn surviving E_6 skill books into 7★ (red frame).
    # Recompute fixed secondary stats when the template star changes; keep
    # level, enchant, alchemy and halo progress.
    _norm_changed_ids = set()
    _norm_deleted_ids = set()
    for _iid in list(my.keys()):
        _inst = my.get(_iid)
        if not isinstance(_inst, dict):
            continue
        _eid = _inst.get("eid")
        if not isinstance(_eid, str):
            continue
        try:
            _tpl_star = int(_eid.split("_")[2])
            if _tpl_star > 100:
                _tpl_star //= 10000
        except (IndexError, TypeError, ValueError):
            _tpl_star = 1
        if _tpl_star <= 4:
            del my[_iid]
            _norm_changed_ids.add(_iid)
            _norm_deleted_ids.add(_iid)
            continue
        _final = _final_equip_eid(_eid)
        if _final != _eid:
            _inst["eid"] = _final
            _inst["new_4attrs"] = _fixed_equip_attrs(_final)
            _inst["attrs_v2"] = True
            _inst.pop("attrs_v3", None)
            _norm_changed_ids.add(_iid)
    if _norm_changed_ids:
        _pend = acc.get("equip_wash_pending")
        if isinstance(_pend, dict) and _pend.get("eqid") in _norm_changed_ids:
            acc.pop("equip_wash_pending", None)
    if _norm_deleted_ids:
        _rows = acc.get("as_equips")
        if isinstance(_rows, list):
            for _row in _rows:
                if isinstance(_row, list):
                    for _ri, _rid in enumerate(_row):
                        if _rid in _norm_deleted_ids:
                            _row[_ri] = None
    # 2026-10-22: E_4023 (無羈之鍪) affixes changed from flee+tough to
    # hit+tough.  Rebuild existing copies once so already-6★ instances pick
    # up the new pair; wash progress is carried over proportionally.
    if not acc.get("equip_bond_affix_v1"):
        for _inst in my.values():
            if not isinstance(_inst, dict):
                continue
            _eid = _inst.get("eid")
            if not (isinstance(_eid, str) and _eid.startswith("E_4023_")):
                continue
            _base = _fixed_equip_attrs(_eid)
            _inst["affix_base"] = dict(_base)
            try:
                _done = max(0, min(_EQUIP_WASH_CLICKS,
                                   int(_inst.get("wash_done", 0) or 0)))
            except (TypeError, ValueError):
                _done = 0
            _attrs = dict(_base)
            for _key, _weight in _EQUIP_WASH_MAX.items():
                if _base.get(_key, 0):
                    _attrs[_key] = round(
                        _base[_key]
                        + _weight * _done / float(_EQUIP_WASH_CLICKS), 4)
            _inst["new_4attrs"] = _attrs
        acc["equip_bond_affix_v1"] = True
    # 2026-10-23: weapon roles + critdmg cap rebalance.  Rebuild every
    # instance's affix base and wash progress from the new template data so
    # existing 6★/7★ gear picks up the new pairs and the 50%/+25% critdmg.
    if not acc.get("equip_weapon_affix_v2"):
        for _inst in my.values():
            if not isinstance(_inst, dict):
                continue
            _eid = _inst.get("eid")
            if not isinstance(_eid, str):
                continue
            _base = _fixed_equip_attrs(_eid)
            _inst["affix_base"] = dict(_base)
            try:
                _done = max(0, min(_EQUIP_WASH_CLICKS,
                                   int(_inst.get("wash_done", 0) or 0)))
            except (TypeError, ValueError):
                _done = 0
            _attrs = dict(_base)
            for _key, _weight in _EQUIP_WASH_MAX.items():
                if _base.get(_key, 0):
                    _attrs[_key] = round(
                        _base[_key]
                        + _weight * _done / float(_EQUIP_WASH_CLICKS), 4)
            _inst["new_4attrs"] = _attrs
        acc.pop("equip_wash_pending", None)
        acc["equip_weapon_affix_v2"] = True
    # 2026-10-23 second pass: E_1502/E_1503 became tank weapons and E_3010
    # switched to dodge + crit resistance.  Rebuild those instances once.
    if not acc.get("equip_fiddle_v1"):
        for _inst in my.values():
            if not isinstance(_inst, dict):
                continue
            _eid = _inst.get("eid")
            if not isinstance(_eid, str) or not _eid.startswith(
                    ("E_1502_", "E_1503_", "E_3010_")):
                continue
            _base = _fixed_equip_attrs(_eid)
            _inst["affix_base"] = dict(_base)
            try:
                _done = max(0, min(_EQUIP_WASH_CLICKS,
                                   int(_inst.get("wash_done", 0) or 0)))
            except (TypeError, ValueError):
                _done = 0
            _attrs = dict(_base)
            for _key, _weight in _EQUIP_WASH_MAX.items():
                if _base.get(_key, 0):
                    _attrs[_key] = round(
                        _base[_key]
                        + _weight * _done / float(_EQUIP_WASH_CLICKS), 4)
            _inst["new_4attrs"] = _attrs
        acc.pop("equip_wash_pending", None)
        acc["equip_fiddle_v1"] = True
    # 2026-10-25: hit/flee affixes are halved (base + wash weights together).
    # Rebuild every instance's affix base and wash progress from the new
    # templates; crit / critdmg / tough keep their original values.
    if not acc.get("equip_hitflee_half_v1"):
        for _inst in my.values():
            if not isinstance(_inst, dict):
                continue
            _eid = _inst.get("eid")
            if not isinstance(_eid, str):
                continue
            _base = _fixed_equip_attrs(_eid)
            _inst["affix_base"] = dict(_base)
            try:
                _done = max(0, min(_EQUIP_WASH_CLICKS,
                                   int(_inst.get("wash_done", 0) or 0)))
            except (TypeError, ValueError):
                _done = 0
            _attrs = dict(_base)
            for _key, _weight in _EQUIP_WASH_MAX.items():
                if _base.get(_key, 0):
                    _attrs[_key] = round(
                        _base[_key]
                        + _weight * _done / float(_EQUIP_WASH_CLICKS), 4)
            _inst["new_4attrs"] = _attrs
        acc.pop("equip_wash_pending", None)
        acc["equip_hitflee_half_v1"] = True
    # 2026-10-25: enchant values scaled x0.35 with the new dust caps.  This
    # runs before the cap clamp below so previously-capped slots land on the
    # new cap instead of being clamped then scaled twice.
    if not acc.get("magic_scale_v1"):
        for _inst in my.values():
            if not isinstance(_inst, dict):
                continue
            _mg = _inst.get("magic")
            if isinstance(_mg, list):
                _inst["magic"] = [
                    int(round(float(_x or 0) * 0.35)) for _x in _mg[:4]]
        acc["magic_scale_v1"] = True
    # Low-star fragments/souls are now dead weight; remove them too so the
    # compose/soul panels cannot recreate deleted blue items.
    for _fld in ("fragment_equips", "equip_soul"):
        _bag = acc.get(_fld)
        if not isinstance(_bag, dict):
            continue
        for _key in list(_bag.keys()):
            try:
                _ks = int(str(_key).split("_")[2])
                if _ks > 100:
                    _ks //= 10000
            except (IndexError, TypeError, ValueError):
                continue
            if _ks <= 4:
                del _bag[_key]
    # symp is the enchant colour (0..3); the client renders it through
    # Equip.getSympStr() -> MainConfig.$magic_two (31020..31024).  Only
    # clamp out-of-range values, otherwise PanelEquipMagic crashes when
    # re_add_magic feeds TXT_SYMP[-1] into getLanguageStr().
    for inst in my.values():
        if isinstance(inst, dict):
            try:
                sp = int(inst.get("symp", -1))
            except (TypeError, ValueError):
                sp = -1
            inst["symp"] = sp if 0 <= sp <= 3 else -1
    # Enchant slots: 0 green HP (1200), 1 blue AP (800),
    # 2 purple HP (3600), 3 orange AP (2400).  Clamp old 999-capped saves.
    try:
        _dust_max = (_cfg()["system_simple"].get("dust") or {}).get("max") \
            or [1200, 800, 3600, 2400, 999]
    except (TypeError, ValueError):
        _dust_max = [1200, 800, 3600, 2400, 999]
    for inst in my.values():
        if not isinstance(inst, dict):
            continue
        mg = inst.get("magic")
        if not isinstance(mg, list) or len(mg) < 4:
            mg = [0, 0, 0, 0]
        else:
            try:
                mg = [max(0, int(x or 0)) for x in mg[:4]]
            except (TypeError, ValueError):
                mg = [0, 0, 0, 0]
        for _i in range(4):
            try:
                _cap = int(_dust_max[_i])
            except (TypeError, ValueError, IndexError):
                _cap = 9999
            if mg[_i] > _cap:
                mg[_i] = _cap
        inst["magic"] = mg
    # Every equipment carries alchemy progress [type, step] on the original
    # server; PanelEquipAlchemyStart dereferences it unconditionally.
    for inst in my.values():
        if isinstance(inst, dict):
            al = inst.get("alchemy")
            if (not isinstance(al, list) or len(al) < 2):
                inst["alchemy"] = [0, 0]
    # Halo is a five-colour track: white, green, blue, purple, orange.
    # Equipment starts with NO halo (lv 0) and the first wash upgrades it
    # to the white lv1 ring.  Four bars take lv0 to the lv5 cap; each bar
    # needs equipwash[6 + lv - 1] washes and surplus carries over.
    try:
        _halo_cfg = _cfg()["system_simple"].get("equipwash") or []
        _halo_cap = int(_halo_cfg[5]) if len(_halo_cfg) > 5 else 5
    except (TypeError, ValueError, IndexError):
        _halo_cap = 5
    _halo_reset_exp = not acc.get("halo_v2_migrated")
    _halo_zero = not acc.get("halo_zeroed_v1")
    for inst in my.values():
        if not isinstance(inst, dict):
            continue
        halo = inst.get("halo")
        if not isinstance(halo, dict):
            halo = {"lv": 0, "exp": 0}
            inst["halo"] = halo
        try:
            lv = max(0, int(halo.get("lv", 0)))
            exp = max(0, int(halo.get("exp", 0)))
        except (TypeError, ValueError):
            lv, exp = 0, 0
        if _halo_reset_exp:
            exp = 0
        # One-time migration: old accounts seeded every item at the white
        # lv1 ring.  Untouched items (exp 0) drop back to no halo; items
        # that were actually washed keep their progress.
        if _halo_zero and lv == 1 and exp == 0:
            lv = 0
        if lv >= _halo_cap:
            lv, exp = _halo_cap, 0
        halo["lv"], halo["exp"] = lv, exp
    if _halo_reset_exp:
        acc["halo_v2_migrated"] = True
    if _halo_zero:
        acc["halo_zeroed_v1"] = True
    # 2026-10-21: equipment secondary stats are now fixed by type/star.
    # crit/tough are 0.1% units (6★ = 60 -> 6%), critdmg is percent
    # (6★ = 18 -> +18% crit damage).  hit/flee remain rating points.
    # attrs_v2 overwrites the old star*3 / level-scaled values exactly once.
    for inst in my.values():
        if not isinstance(inst, dict):
            continue
        if inst.get("attrs_v2"):
            continue
        inst["new_4attrs"] = _fixed_equip_attrs(inst.get("eid"))
        inst["attrs_v2"] = True
    # 2026-10-21 v3: max-level affix values, deterministic 255-click wash,
    # halo reset.  All old wash/quality values are replaced once.
    for inst in my.values():
        if not isinstance(inst, dict):
            continue
        if inst.get("attrs_v3"):
            continue
        _base = _fixed_equip_attrs(inst.get("eid"))
        inst["affix_base"] = dict(_base)
        inst["new_4attrs"] = dict(_base)
        inst["wash_done"] = 0
        inst["attrs_v3"] = True
        inst["halo"] = {"lv": 0, "exp": 0}
    # 2026-10-22: a fully washed (255-click) item must always carry the max
    # halo.  Old saves accumulated halo exp with a wrong first-bar cost
    # (equipwash[5] instead of equipwash[6]), so 255 clicks left some items
    # one bar short and 保存 dropped the display from 5级 back to 4级.
    if not acc.get("halo_fullwash_v1"):
        for inst in my.values():
            if not isinstance(inst, dict):
                continue
            try:
                _done = int(inst.get("wash_done", 0) or 0)
            except (TypeError, ValueError):
                _done = 0
            if _done >= _EQUIP_WASH_CLICKS:
                inst["halo"] = {"lv": _halo_cap, "exp": 0}
        acc["halo_fullwash_v1"] = True
    rows = acc.get("as_equips")
    if not isinstance(rows, list):
        rows = []
    norm = []
    for i in range(5):
        row = rows[i] if i < len(rows) and isinstance(rows[i], list) else []
        row = list(row[:6])
        row += [None] * (6 - len(row))
        norm.append(row)
    # Equipment instance ids must start with a lowercase "e": the client
    # distinguishes instances from E_* templates with indexOf("e") in
    # PanelEquipBook and several other panels.  Older saves used "Q%d".
    renames = {}
    for iid in list(my):
        if isinstance(iid, str) and iid.startswith("Q"):
            new = "e" + iid[1:]
            while new in my:
                new += "0"
            renames[iid] = new
    if renames:
        for old, new in renames.items():
            my[new] = my.pop(old)
        for row in norm:
            for i, val in enumerate(row):
                if val in renames:
                    row[i] = renames[val]
    acc["as_equips"] = norm
    return my, norm


def _ensure_fragments(acc):
    """user.fragment["equips"]: fragment id -> array of piece slots (0/1).

    2026-10-24: the hero/equipment fragment systems are disabled.  Any
    fragments already on the account are cleared once and the panel keeps
    returning an empty map, so nothing can be composed or dropped.
    """
    if not acc.get("fragments_disabled_v1"):
        acc["fragment_equips"] = {}
        acc["fragments_disabled_v1"] = True
    return {}


def _shop_state(acc, s_type):
    """Per-tab mystery-shop state; regenerates after refresh_interval."""
    cfg = _cfg()["mystery_shop"].get(s_type, {})
    interval = int(cfg.get("refresh_interval", 60)) * 60000
    now = _now_ms()
    shops = acc.setdefault("mystery_shop", {})
    # Discard the old avatar/material offers once; the new shop is
    # equipment-only (normal/advanced) or two exchange goods (super).
    if not acc.get("mystery_shop_v3"):
        shops.clear()
        acc["mystery_shop_v3"] = True
    # 2026-10-24: regenerate once so the new per-type prices replace the
    # old saved 8000-點券 offers.
    if not acc.get("mystery_shop_v4"):
        shops.clear()
        acc["mystery_shop_v4"] = True
    # 2026-10-24: super tab gained the 四色粉塵×1000 offer.
    if not acc.get("mystery_shop_v5"):
        shops.clear()
        acc["mystery_shop_v5"] = True
    st = shops.get(s_type)
    if (not isinstance(st, dict) or not isinstance(st.get("items"), list)
            or now - int(st.get("t", 0)) > interval):
        st = _gen_shop(acc, s_type, now)
        shops[s_type] = st
    # Migrate old saved offers that embedded a whole instance dict: the
    # client can only render template-id equip offers before purchase.
    for item in st.get("items", []):
        if not (isinstance(item, list) and item and isinstance(item[0], dict)):
            continue
        av = item[0].get("avatar")
        if isinstance(av, dict):
            for k, val in list(av.items()):
                if isinstance(val, dict) and "lv" in val:
                    av[k] = 1
        eq = item[0].get("equip")
        if isinstance(eq, dict):
            for k, val in list(eq.items()):
                if isinstance(val, dict) and isinstance(val.get("eid"), str):
                    item[0]["equip"] = {val["eid"]: 1}
                    break
                parts = k.split("_") if isinstance(k, str) else []
                if len(parts) == 3 and len(parts[2]) == 5 and parts[2].isdigit():
                    short = "E_%s_%d" % (parts[1], int(parts[2]) // 10000)
                    if short in EQUIP_CATALOG:
                        eq[short] = val
                        del eq[k]
    return st


def _gen_shop(acc, s_type, now_ms):
    """Mystery shop (2026-10-22 user rules).

    normal   : every 6★ equipment template, 8000 點券 each
    advanced : every 7★ skill-book template, 9000 點券 each
    super    : two exchange goods, 3000 點券 -> 200,000 gold and
               200,000 gold -> 3000 點券 (金磚 is the same premium pool).
    """
    items = []
    if s_type == "super":
        items.append([{"gold": 200000}, {"coin": 3000}])
        items.append([{"coin": 3000}, {"gold": 200000}])
        # 2026-10-24: 四色粉塵×1000, 1000 點券 (grants 1000 of each colour).
        items.append([{"dust": [1000, 1000, 1000, 1000, 0]},
                      {"coin": 1000}])
        return {"t": now_ms, "items": items, "b": []}
    if s_type == "advanced":
        pool = sorted(
            eid for eid, meta in EQUIP_CATALOG.items()
            if str(meta.get("type")) == "6"
            and len(eid.split("_")) == 3 and eid.split("_")[2] == "7"
        )
    else:
        pool = sorted(
            eid for eid, meta in EQUIP_CATALOG.items()
            if str(meta.get("type")) != "6"
            and len(eid.split("_")) == 3 and eid.split("_")[2] == "6"
        )
    for eid in pool:
        # Template id, not an instance id: ItemSoulShop resolves it through
        # cfg.equip and materialises a fresh instance on purchase.
        if s_type == "advanced":
            price = 9000
        else:
            # 2026-10-24 user rule: weapon/accessory 8000, armour 6500,
            # boots 3000 點券.
            etype = str((EQUIP_CATALOG.get(eid) or {}).get("type", ""))
            price = {"3": 6500, "5": 3000}.get(etype, 8000)
        items.append([{"equip": {eid: 1}}, {"coin": price}])
    return {"t": now_ms, "items": items, "b": []}


def _owned_aids(avatars):
    return {k.split("|")[0] for k in avatars}


def _note_avatar_soul(acc, aid):
    """A duplicate hero card converts into one 英雄戰魂."""
    souls = acc.setdefault("avatar_soul", {})
    souls[aid] = int(souls.get(aid, 0)) + 1


def _new_avatar_instance(aid):
    """Build a fresh account avatar instance (used by the GM grant helper)."""
    aid = _low_star_clamp(aid)
    return {
        "lv": 1, "exp": 0, "slv": 1, "star": _avatar_star(aid),
        "love": 0, "phase": 0, "morph": 0, "limit_break": 0,
        "love_exp": 0,
        "tpl": [2, 1, 1, 330, 300],
        "hp": 0, "ap": 0, "de_ph": 0, "de_ma": 0,
    }


def _grant_gift(acc, gift):
    """Apply a task/daily-gift reward dict to the account."""
    if not isinstance(gift, dict):
        return
    avatars = _ensure_avatars(acc)
    my, _rows = _ensure_equips(acc)
    for key, val in gift.items():
        if key == "score":
            # 2026-10-23: score (friendship/victory) gains are disabled.
            continue
        if key in ("gold", "coin", "medal", "mark",
                   "box_key", "dn_stone", "guild_contribute",
                   "energy_extra", "attr_energy_extra",
                   "fragment_energy_extra"):
            dest = "energy_extra" if key == "attr_energy_extra" else key
            acc[dest] = int(acc.get(dest, 0)) + int(val)
        elif key == "avatar" and isinstance(val, dict):
            owned = _owned_aids(avatars)
            for k, av in val.items():
                aid = k.split("|")[0]
                if aid in owned:
                    _note_avatar_soul(acc, aid)
                avatars[k] = av
        elif key == "equip" and isinstance(val, dict):
            for k, inst in val.items():
                my[k] = inst
        elif key == "fragment" and isinstance(val, dict):
            frags = _ensure_fragments(acc)
            for k, arr in val.items():
                frags[k] = arr
        elif key == "avatar_soul" and isinstance(val, dict):
            souls = acc.setdefault("avatar_soul", {})
            for k, n in val.items():
                souls[k] = int(souls.get(k, 0)) + int(n)
        elif key == "equip_soul" and isinstance(val, dict):
            souls = acc.setdefault("equip_soul", {})
            for k, n in val.items():
                souls[k] = int(souls.get(k, 0)) + int(n)
        elif key == "dust":
            # Dust is a four-colour currency array, not an item id.
            # Accept either [g,b,p,o] or {indexID_s:i, numberIndex:n}.
            dust = acc.get("dust_arr")
            if not isinstance(dust, list) or len(dust) < 5:
                dust = [0, 0, 0, 0, 0]
                acc["dust_arr"] = dust
            if isinstance(val, list):
                for i, n in enumerate(val[:len(dust)]):
                    dust[i] = int(dust[i]) + int(n or 0)
            elif isinstance(val, dict):
                try:
                    i = int(val.get("indexID_s"))
                    n = int(val.get("numberIndex") or 0)
                except (TypeError, ValueError):
                    i = -1
                if 0 <= i < len(dust):
                    dust[i] += n
        elif key == "culture_book":
            acc["culture_book"] = int(acc.get("culture_book", 0)) + int(val)


# --------------------------------------------------------------------------- #
# 系統郵件 (mailbox resource distribution)
#
# PanelSocialMail / ItemSocialMail (index == 3) read user.get_msg.gift_msg:
#   { "<id>": {status, info_type, info_data, gift_dict, time, uid}, ... }
# and claim with user.get_gift_msg {gk: "<id>"}.  gift_dict is also passed to
# GlobalFunction.getAwardByType() for the reward preview, so avatar values use
# the display form { "<aid>|<slot>": count }.  Claiming expands them into real
# avatar instances (one slot each).
# --------------------------------------------------------------------------- #
SYS_MAIL_UID = "sys"
STARTER_MAIL_ID = "0001"
STARTER_MAIL = {
    "gold": 5000000,
    "coin": 50000,
    "avatar": {
        "A_6996_4|9901": 30,   # 武鬥密卷-中 (50k EXP each)
        "A_6992_4|9902": 10,   # 技能餅乾-大
        "A_2300_4|9903": 10,   # 經驗材料
    },
}
# 2026-10-24 開服禮包: sent once to every account (existing and new).
LAUNCH_GIFT_ID = "9001"
LAUNCH_GIFT = {
    "coin": 200000,
    "gold": 10000000,
    "dust": [2000, 2000, 2000, 2000, 0],   # 四色粉塵各 2000
    "avatar": {
        "A_1001_5|9101": 1,   # 5★ 凱倫
        "A_1002_5|9102": 1,   # 5★ 艾夕
        "A_1003_5|9103": 1,   # 5★ 瑞澤
    },
}
# 2026-10-25: launch-gift materials, one mail per material type.
LAUNCH_GIFT_MATERIAL_MAILS = [
    ("9002", "開服禮包·升星材料", {"avatar": {
        "A_6004_2": 5,    # 聚元
        "A_6022_3": 5,    # 破障
        "A_6076_4": 5,    # 啟迪
        "A_6075_5": 3,    # 脫縛
        "A_6994_6": 1,    # 渡厄
    }}),
    ("9003", "開服禮包·技能餅乾", {"avatar": {
        "A_2107_4": 20,   # 技能餅乾-小
        "A_6992_5": 10,   # 技能餅乾-中
        "A_6992_6": 5,    # 技能餅乾-大
    }}),
    ("9004", "開服禮包·魔法藥水", {"avatar": {
        "A_6993_4": 20,   # 魔法藥水-小
        "A_6993_5": 10,   # 魔法藥水-中
        "A_6993_6": 5,    # 魔法藥水-大
    }}),
    ("9005", "開服禮包·神眷秘寶", {"avatar": {
        "A_6999_5": 5,    # 神眷秘寶
    }}),
    # 2026-10-25 follow-up: experience crops.
    ("9006", "開服禮包·經驗材料", {"avatar": {
        "A_6996_5": 10,   # 武鬥密卷-中
        "A_6997_5": 10,   # 魔法真諦-中
        "A_6998_5": 10,   # 真實之書-中
    }}),
]


def _ensure_mailbox(acc):
    """Return the persistent gift-mail dict, restoring persisted Dates."""
    box = acc.get("gift_msgs")
    if not isinstance(box, dict):
        box = {}
        acc["gift_msgs"] = box
    for entry in box.values():
        if not isinstance(entry, dict):
            continue
        t = entry.get("time")
        if isinstance(t, str):
            try:
                entry["time"] = datetime.datetime.fromisoformat(t)
            except ValueError:
                entry["time"] = datetime.datetime.utcnow()
        elif not isinstance(t, datetime.datetime):
            entry["time"] = datetime.datetime.utcnow()
    return box


def _seed_mailbox(acc):
    """Create the one-time starter resource mail (idempotent)."""
    box = _ensure_mailbox(acc)
    # 2026-10-24: fixed launch gift for every player.  Seeded for existing
    # saves too (mail_seeded is already 1 on those accounts).
    if not acc.get("launch_gift_seeded_v1"):
        acc["launch_gift_seeded_v1"] = 1
        if LAUNCH_GIFT_ID not in box:
            box[LAUNCH_GIFT_ID] = {
                "status": 0,
                "info_type": 99003,
                "info_data": "開服禮包",
                "gift_dict": dict(LAUNCH_GIFT),
                "time": datetime.datetime.utcnow(),
                "uid": SYS_MAIL_UID,
            }
    # 2026-10-25: extra launch-gift material mails (one per material type).
    # Seeded independently so existing accounts receive them too.  v2 also
    # adds the 9006 experience-material mail to accounts that already had v1.
    if not acc.get("launch_gift_materials_v2"):
        acc["launch_gift_materials_v2"] = 1
        acc["launch_gift_materials_v1"] = 1
        for _mid, _title, _gift in LAUNCH_GIFT_MATERIAL_MAILS:
            if _mid in box:
                continue
            box[_mid] = {
                "status": 0,
                "info_type": 99003,
                "info_data": _title,
                "gift_dict": dict(_gift),
                "time": datetime.datetime.utcnow(),
                "uid": SYS_MAIL_UID,
            }
    if acc.get("mail_seeded"):
        return box
    acc["mail_seeded"] = 1
    if STARTER_MAIL_ID not in box:
        box[STARTER_MAIL_ID] = {
            "status": 0,
            "info_type": 99003,
            "info_data": "",
            "gift_dict": dict(STARTER_MAIL),
            "time": datetime.datetime.utcnow(),
            "uid": SYS_MAIL_UID,
        }
    return box


def _next_mail_id(acc):
    n = int(acc.get("next_mail", 2))
    acc["next_mail"] = n + 1
    return "%04d" % n


def _add_mail(acc, gift, info_type=99001, info_data="", uid=SYS_MAIL_UID):
    """Queue a gift mail; returns its id."""
    box = _ensure_mailbox(acc)
    mid = _next_mail_id(acc)
    box[mid] = {
        "status": 0,
        "info_type": int(info_type),
        "info_data": str(info_data or ""),
        "gift_dict": gift if isinstance(gift, dict) else {},
        "time": datetime.datetime.utcnow(),
        "uid": uid,
    }
    return mid


def _grant_mail_gift(acc, gift):
    """Claim-time grant: avatar counts become one instance per copy."""
    if not isinstance(gift, dict):
        return
    rest = dict(gift)
    av_gift = rest.pop("avatar", None)
    if isinstance(av_gift, dict):
        avatars = _ensure_avatars(acc)
        owned = _owned_aids(avatars)
        slot = int(acc.get("next_slot", 100))
        for key, val in av_gift.items():
            # Old all-catalog mails carry synthetic low-star ids; claim them
            # as the family's lowest real tier instead.
            aid = _low_star_clamp(str(key).split("|")[0])
            if isinstance(val, dict):
                # Already an account avatar instance (legacy/other callers).
                avatars[str(key)] = dict(val)
                owned.add(aid)
                continue
            try:
                count = max(1, int(val or 1))
            except (TypeError, ValueError):
                count = 1
            # Mail gifts always materialise as real avatar instances, even
            # when the same hero is already owned.  (Gacha/shop duplicates
            # still turn into 英雄戰魂; the mailbox is a test/reward source.)
            for _ in range(count):
                key_new = "%s|%d" % (aid, slot)
                slot += 1
                avatars[key_new] = _new_avatar_instance(aid)
                owned.add(aid)
        acc["next_slot"] = slot
    _grant_gift(acc, rest)


def _gift_user_payload(acc):
    """Fields ItemSocialMail.re_gift_msg() copies into GlobalData.$userData."""
    user = make_user(acc)
    attrs = user.get("attrs") or {}
    return {
        "guild_contribute": int(acc.get("guild_contribute", 0)),
        "avatars": user.get("avatars") or {},
        "my_equips": user.get("my_equips") or {},
        "gold": int(user.get("gold", 0)),
        "score": int(user.get("score", 0)),
        "medal": int(user.get("medal", 0)),
        "mark": int(user.get("mark", 0)),
        "coin": int(user.get("coin", 0)),
        "dust": attrs.get("dust") or [0, 0, 0, 0, 0],
        "attr_energy_extra": int(attrs.get("energy_extra", 0)),
        "dn_stone": int(user.get("dn_stone", 0)),
        "energy": user.get("energy"),
        "fragment_energy": user.get("fragment_energy"),
        "box_key": int(acc.get("box_key", 0)),
        "exp": int(user.get("exp", 0)),
        "avatar_soul": user.get("avatar_soul") or {},
        "equip_soul": user.get("equip_soul") or {},
        "culture_book": int(attrs.get("culture_book", 0)),
        "sp": list(attrs.get("sp") or []),
        "lv": int(user.get("lv", 25)),
        "avatar_num": len(user.get("avatars") or {}),
    }


SIGN_IN_REWARD_SCALE = 2000


def _check_in_cfg():
    """PanelEveryDaySign: check_in[month] = [{reward, vip_double}, ...].

    2026-10-25 user request: every daily reward on the sign-in board is
    multiplied by 2000 (day 1 = 200,000 gold; day 7 = 240,000 點券).
    """
    months = {}
    for month in range(1, 13):
        days = []
        for day in range(1, 15):
            if day % 7 == 0:
                reward = {"coin": (50 + day * 10) * SIGN_IN_REWARD_SCALE}
            else:
                reward = {"gold": 100 * day * SIGN_IN_REWARD_SCALE}
            days.append({"reward": reward, "vip_double": 0})
        months[str(month)] = days
    return months


def _check_in_state(acc):
    st = acc.get("check_in")
    if not isinstance(st, dict):
        st = {}
    st.setdefault("m", 1)
    st.setdefault("n", 0)
    hc = st.get("had_check")
    if not (isinstance(hc, list) and len(hc) >= 2):
        st["had_check"] = [0, 0]
    today = datetime.date.today().isoformat()
    if acc.get("check_in_day") != today:
        st["had_check"] = [0, 0]
        acc["check_in_day"] = today
    cfg = _cfg()["check_in"].get(str(st["m"]))
    if isinstance(cfg, list) and cfg and int(st["n"]) >= len(cfg):
        st["m"] = int(st["m"]) + 1 if int(st["m"]) < 12 else 1
        st["n"] = 0
    acc["check_in"] = st
    return st


def _avatar_next_exp(aid, lv, extra_cap=0):
    """Mirror Avatar.getNextExp(): expRate * (a*lv² + b*lv + c)."""
    curve = _cfg()["system_simple"]["avatar_exp"]
    a, b, c = int(curve[0]), int(curve[1]), int(curve[2])
    av = _cfg()["avatar"].get(aid) or {}
    rate = (av.get("tl") or [0, 0, 0, 0, 10, 1])[5]
    lv_max = (av.get("tl") or [0, 0, 0, 0, 10])[4] + int(extra_cap)
    if lv >= lv_max:
        return 2147483647
    return int(rate * (a * lv * lv + b * lv + c))


def _avatar_all_exp(aid, lv, exp):
    """Mirror Avatar.getAllExp(lv) + exp (the value used by getOfferExp)."""
    curve = _cfg()["system_simple"]["avatar_exp"]
    a, b, c = int(curve[0]), int(curve[1]), int(curve[2])
    av = _cfg()["avatar"].get(aid) or {}
    rate = (av.get("tl") or [0, 0, 0, 0, 10, 1])[5]
    total = (a / 3.0 * lv ** 3 + (b - a) / 2.0 * lv ** 2
             + (a / 6.0 - b / 2.0 + c) * lv - c) * rate
    return int(total) + int(exp)


def _avatar_offer_exp(key, avatar):
    """Mirror Avatar.getOfferExp(): swallowed material EXP + flat offerExp."""
    aid = key.split("|")[0]
    star = max(1, _avatar_star(aid))
    provide = _cfg()["system_simple"]["provide_exp"]
    factor = provide[star - 1] if star - 1 < len(provide) else 1
    flat = ((_cfg()["avatar"].get(aid) or {}).get("tl")
            or [0, 0, 0, 0, 10, 1, 100])[6]
    return int(_avatar_all_exp(aid, int(avatar.get("lv", 1)),
                               int(avatar.get("exp", 0))) * factor + flat)


_EQUIP_CFG = None


def _equip_cfg():
    """EQUIP_CATALOG plus skill ids for type-6 books.

    Equip.getBookSkill() returns null when equipData.skill is empty, and
    PanelEquipBook then calls .getInfo() on it (#1009).  Give every book
    template a real skill id.
    """
    global _EQUIP_CFG
    if _EQUIP_CFG is None:
        out = {}
        for eid, meta in EQUIP_CATALOG.items():
            entry = dict(meta)
            pl = list(entry.get("pl") or [])
            while len(pl) < 10:
                pl.append("" if len(pl) in (6, 7, 8) else 0)
            if str(eid).startswith("E_6505_"):
                # 神技：天火 carries the custom 三昧真火 active skill.
                pl[8] = "S_9850_1"
                pl[9] = 0
            elif str(eid).startswith("E_6009_"):
                # 神技：地狱星 carries the custom 地獄陨落 active skill.
                pl[8] = "S_9851_1"
                pl[9] = 0
            elif str(eid).startswith("E_6201_"):
                # 魔技：惡魔契約 carries the custom 戾伐之償 active skill.
                pl[8] = "S_9852_1"
                pl[9] = 0
            elif str(eid).startswith("E_6001_"):
                # 狂暴復甦 carries the passive 生命源泉 book skill.
                pl[8] = "S_9853_1"
                pl[9] = 0
            # 2026-10-24 skill-book redesign (user rules).
            elif str(eid).startswith("E_6501_"):
                pl[8] = "S_9854_1"; pl[9] = 0      # 神技：狙殺
            elif str(eid).startswith("E_6502_"):
                pl[8] = "S_9855_1"; pl[9] = 0      # 神技：突襲
            elif str(eid).startswith("E_6503_"):
                pl[8] = "S_9856_1"; pl[9] = 0      # 神技：湧動
            elif str(eid).startswith("E_6504_"):
                pl[8] = "S_9857_1"; pl[9] = 0      # 神技：鐵腕
            elif str(eid).startswith("E_6506_"):
                pl[8] = "S_9858_1"; pl[9] = 0      # 神技：堅定
            elif str(eid).startswith("E_6010_"):
                pl[8] = "S_9859_1"; pl[9] = 0      # 魔技：獻祭
            elif str(eid).startswith("E_6002_"):
                pl[8] = "S_9860_1"; pl[9] = 0      # 狂暴兇殺術
            elif str(eid).startswith("E_6003_"):
                pl[8] = "S_9861_1"; pl[9] = 0      # 狂暴裂甲
            elif str(eid).startswith("E_6004_"):
                pl[8] = "S_9862_1"; pl[9] = 0      # 狂暴鐵壁
            elif str(eid).startswith("E_6005_"):
                pl[8] = "S_9863_1"; pl[9] = 0      # 鷹眼精準術
            elif str(eid).startswith("E_6006_"):
                pl[8] = "S_9864_1"; pl[9] = 0      # 無影靈巧術
            elif str(eid).startswith("E_6007_"):
                pl[8] = "S_9865_1"; pl[9] = 0      # 狂暴致命
            elif str(eid).startswith("E_6008_"):
                pl[8] = "S_9866_1"; pl[9] = 0      # 狂暴攔截
            elif str(entry.get("type")) == "6" and not pl[8]:
                # S_1000_1 is the skill every battle client already resolves
                # (菊花三弄), so it is guaranteed to exist in SkillSetManager.
                pl[8] = "S_1000_1"
                pl[9] = 0
            entry["pl"] = pl
            out[eid] = entry
        _EQUIP_CFG = out
    return _EQUIP_CFG


def _equip_star(eid):
    try:
        return max(1, int(str(eid).split("_")[2]))
    except (IndexError, ValueError):
        return 1


def _equip_effective_star(inst):
    """Mirror Equip.getStar(): template star + alchemy step.

    Equip.getStar() = int(id.split("_")[2]) + my_data.alchemy[1].  Wash
    costs, halo exp requirements and rise prices all use that value on the
    client, so the server must use it too; otherwise an alchemised item's
    progress bar advances at a different rate than the client shows.
    """
    if not isinstance(inst, dict):
        return 1
    star = _equip_star(inst.get("eid"))
    al = inst.get("alchemy")
    if isinstance(al, (list, tuple)) and len(al) > 1:
        try:
            star += int(al[1])
        except (TypeError, ValueError):
            pass
    return max(1, star)


def _equip_add_halo(inst, stars, gain):
    """Mirror Equip.addHaloExp(): one point per wash, surplus carries over.

    Bars 1..4 need equipwash[6..9] washes; when those entries are missing,
    fall back to the old equipwash[0] * 1.2^lv * star curve.
    """
    cfg = _cfg()["system_simple"]["equipwash"]
    cap = int(cfg[5])
    halo = inst.setdefault("halo", {"lv": 0, "exp": 0})
    lv = max(0, int(halo.get("lv", 0)))
    exp = int(halo.get("exp", 0)) + int(gain)
    while lv < cap:
        # Mirror Equip.getHaloExpMax(): lv0 and lv1 both use equipwash[6]
        # (22), then lv2/3/4 use equipwash[7/8/9] (47/77/109).
        idx = 6 if lv <= 1 else lv + 5
        try:
            need = int(cfg[idx])
        except (IndexError, TypeError, ValueError):
            need = 0
        if need <= 0:
            need = max(1, int(int(cfg[0]) * (float(cfg[1]) ** lv) * stars))
        if exp < need:
            break
        exp -= need
        lv += 1
    if lv >= cap:
        lv, exp = cap, 0
    halo["lv"], halo["exp"] = lv, exp


def _avatar_sell_value(key, avatar):
    """Approximate Avatar.getSellValue() for 軍營 > 出售 payouts."""
    aid = key.split("|")[0]
    tl = ((_cfg()["avatar"].get(aid) or {}).get("tl")
          or [0] * 9)
    offer_gold = float(tl[7] if len(tl) > 7 else 200)
    offer_exp = float(_avatar_offer_exp(key, avatar) or 0)
    if offer_exp > 0:
        value = (min(10.0, offer_gold / offer_exp) * 200
                 + max(-offer_exp * 0.1, offer_gold - offer_exp)
                 + offer_gold * 0.001 + 250)
    else:
        value = offer_gold + 250
    try:
        type_ = int(aid[2]) if aid[2].isdigit() else 1
    except IndexError:
        type_ = 1
    if type_ == 1:
        value -= 10000000
    lv = int(avatar.get("lv", 1))
    value -= lv * 1000 if lv > 10 else lv
    value -= _avatar_star(aid) * 100
    value -= int(avatar.get("phase", 0)) * 10000
    value -= max(0, int(avatar.get("slv", 1)) - 1) * 10000
    value -= int(avatar.get("love_exp", 0)) * 60000
    if int(avatar.get("morph", 0)) > 0:
        value -= 7000000
    try:
        value += 0.001 * int(aid.split("_")[1])
    except (IndexError, ValueError):
        pass
    return max(0, int(value))


def _grant_avatar_exp(aid, avatar, amount):
    """Apply material EXP and level up using the same curve as the client."""
    total = int(avatar.get("exp", 0)) + int(amount)
    lv = int(avatar.get("lv", 1))
    tl = (_cfg()["avatar"].get(aid) or {}).get("tl") \
        or [0, 0, 0, 0, 10]
    extra_cap = 30 if int(avatar.get("limit_break", 0) or 0) else 0
    lv_max = tl[4] + extra_cap
    while lv < lv_max:
        need = _avatar_next_exp(aid, lv, extra_cap)
        if need <= 0 or total < need:
            break
        total -= need
        lv += 1
    avatar["lv"] = lv
    avatar["exp"] = total


def _ms_dt(ms):
    """UTC-naive datetime for an AMF Date field, defaulting to now."""
    try:
        ms = int(ms)
    except (TypeError, ValueError):
        ms = 0
    if ms:
        return datetime.datetime.utcfromtimestamp(ms / 1000.0)
    return datetime.datetime.utcnow()


def _ms_dt_epoch(ms):
    """AMF Date for an optional epoch-ms field; missing means 1970."""
    try:
        ms = int(ms)
    except (TypeError, ValueError):
        ms = 0
    if ms <= 0:
        ms = 0
    return datetime.datetime.utcfromtimestamp(ms / 1000.0)


def _sign_cfg():
    """ploy_system_simple.sign_in, keyed by round ("0".."N")."""
    return (_cfg().get("ploy_system_simple") or {}).get("sign_in") or {}


def _sign_state(acc):
    """Return (round, days_signed, last_sign_ms), applying the streak rule.

    PanelActivitySign.checkSignResult() keeps `n` only when the last sign was
    today or yesterday; any longer gap restarts the round at 0.  Mirror that
    server-side so the persisted state cannot drift from the display.
    """
    cfg = _sign_cfg()
    st = acc.setdefault("sign_in", {})
    if not cfg:
        return 0, 0, 0
    try:
        k = int(st.get("k", 0))
    except (TypeError, ValueError):
        k = 0
    if str(k) not in cfg:
        k = 0
    try:
        n = int(st.get("n", 0))
    except (TypeError, ValueError):
        n = 0
    try:
        t = int(st.get("t", 0) or 0)
    except (TypeError, ValueError):
        t = 0
    num = int((cfg.get(str(k)) or {}).get("num", 0))
    if 0 < n < num and t:
        last = datetime.datetime.fromtimestamp(t / 1000.0).date()
        today = datetime.datetime.now().date()
        if last != today and last != today - datetime.timedelta(days=1):
            n = 0
    st["k"], st["n"], st["t"] = k, n, t
    return k, n, t


def _sign_user_obj(acc):
    """Shape for user.attrs.sign_in (client casts .t to Date)."""
    k, n, t = _sign_state(acc)
    return {
        "k": k,
        "n": n,
        "t": datetime.datetime.utcfromtimestamp(t / 1000.0) if t else None,
    }


def _sign_response(acc, gift=None):
    """Full user payload both sign handlers return.

    PanelActivitySign copies a fixed set of fields out of data (avatars,
    my_equips, currencies, sign_in, ...), so start from make_user() and add
    the top-level keys it reads but make_user does not expose there.
    """
    user = make_user(acc)
    user["sign_in"] = user["attrs"]["sign_in"]
    user["gift_dict"] = gift or {}
    user["attr_energy_extra"] = int(user["attrs"].get("energy_extra", 0))
    user["dn_stone"] = int(acc.get("dn_stone", 0))
    user["sp"] = list(_sp_array(acc))
    # PanelActivitySign writes data.dust straight into attrs.dust; it must
    # be the four-colour array, not a scalar.
    user["dust"] = user["attrs"]["dust"]
    user["box_key"] = int(acc.get("box_key", 0))
    user["culture_book"] = int(acc.get("culture_book", 0))
    user["avatar_soul"] = acc.get("avatar_soul", {})
    user["equip_soul"] = acc.get("equip_soul", {})
    return user


# Stage buffs shown by PanelActivityExplorationMyTeam.updateBuffState().
# Each is [attr, class, value, isPercent]: GlobalFunction.getStage_Mode()
# indexes all four, so stage_mode must always be an array of length 4.
_EXPLORATION_MODES = [
    ["hp", "all", 1.2, 1],
    ["ap", "all", 1.3, 1],
    ["de_ph", "all", 1.2, 1],
    ["de_ma", "all", 1.2, 1],
    ["crit", "all", 1.2, 1],
]


def _exploration_state(acc):
    """Normalised 探險 state.

    PanelActivityExplorationMyTeam's constructor does
    `$userData.exploration.combat_army.concat()` and elsewhere indexes
    `.army`, so those keys must exist even before the first team pick.
    stage_mode must be one of _EXPLORATION_MODES (an array), not a number:
    getStage_Mode() reads [0..3] and getStage_Mode(...).data is indexed by
    AvatarImg.updateBuffState().
    """
    st = acc.get("exploration")
    if not isinstance(st, dict):
        st = {}
        acc["exploration"] = st
    st.setdefault("stage", 1)
    st.setdefault("refresh_count", 5)
    st.setdefault("current_stage_finish", 0)
    st.setdefault("mode_buy", 0)
    st.setdefault("relive_buy", 0)
    st.setdefault("vip_relive", 0)
    mode = st.get("stage_mode")
    if not isinstance(mode, list) or len(mode) < 4:
        st["stage_mode"] = list(_EXPLORATION_MODES[0])
    if not isinstance(st.get("army"), dict):
        st["army"] = {}
    ca = st.get("combat_army")
    if (not isinstance(ca, list)
            or any(not isinstance(x, str) for x in ca)):
        # Older saves stored row arrays here; the client expects id strings.
        st["combat_army"] = list(st["army"].keys())
    return st


def _roulette_state(acc):
    """活動中心轉盤 state (PanelActivityRoulette reads attrs.roulette)."""
    st = acc.get("roulette")
    if not isinstance(st, dict):
        st = {}
        acc["roulette"] = st
    st.setdefault("fixed_count", 0)
    # ItemActivityRoulette.check_num indexes fixed_draw[String(max)].
    if not isinstance(st.get("fixed_draw"), dict):
        st["fixed_draw"] = {}
    lt = st.get("last_time")
    if isinstance(lt, str):
        try:
            lt = datetime.datetime.fromisoformat(lt)
        except ValueError:
            lt = None
    if not isinstance(lt, datetime.datetime):
        lt = None
    # The client casts this to Date; a string would crash on next login.
    st["last_time"] = lt
    return st


def _fund_state(acc):
    """活動中心福利基金 state (PanelActivityFund.checkStatus).

    attrs.fund = {key, money, last_time}; attrs.fund_add_time is the
    purchase date.  Real payments never happen offline, so seed a small
    deposit that has already reached its claim window.  Both Date fields
    are persisted as ISO strings by save_accounts() and must be revived
    here or the client's `as Date` cast throws on relogin.
    """
    st = acc.get("fund")
    if not isinstance(st, dict):
        st = {}
        acc["fund"] = st
    st.setdefault("key", "1")
    st.setdefault("money", 1000)
    lt = st.get("last_time")
    if isinstance(lt, str):
        try:
            lt = datetime.datetime.fromisoformat(lt)
        except ValueError:
            lt = None
    if not isinstance(lt, datetime.datetime):
        lt = None
    st["last_time"] = lt
    ft = acc.get("fund_add_time")
    if isinstance(ft, str):
        try:
            ft = datetime.datetime.fromisoformat(ft)
        except ValueError:
            ft = None
    if not isinstance(ft, datetime.datetime):
        # Past the buy window, inside the 7-day claim window.
        ft = datetime.datetime.utcnow() - datetime.timedelta(days=8)
    acc["fund_add_time"] = ft
    return st


def _welfare_state(acc):
    """活動中心福利 state (PanelActivityWelfare)."""
    st = acc.get("welfare")
    if not isinstance(st, dict):
        st = {}
        acc["welfare"] = st
    times = st.get("times")
    if not isinstance(times, list) or len(times) < 4:
        times = [0, 0, 0, 0]
        st["times"] = times
    had = st.get("had_reward")
    if not isinstance(had, list) or len(had) < 4:
        had = [0, 0, 0, 0]
        st["had_reward"] = had
    st.setdefault("coin_times", 0)
    st.setdefault("number", -1)
    st.setdefault("had_play", 0)
    return st


def _sp_array(acc):
    """Talent points, one slot per talent tier (attrs.sp is an array)."""
    sp = acc.get("sp_arr")
    if not isinstance(sp, list):
        old = acc.get("sp")
        sp = [0] * 10
        if isinstance(old, int) and old > 0:
            sp[0] = old
        acc["sp_arr"] = sp
    while len(sp) < 10:
        sp.append(0)
    return sp


def _groupon_data(acc):
    """Shared payload for user.groupon_info / user.groupon_buy."""
    my_num = int(acc.get("groupon_my_num", 0))
    total = int(acc.get("groupon_total", 37))
    consumed = int(acc.get("groupon_consume", 0))
    rows = [{
        "uid": acc.get("uid", "player"), "zone": "1-01",
        "name": str(acc.get("nick") or acc.get("uid") or "Player"),
        "vip_lv": int(acc.get("vip_lv", 0)), "num": my_num,
        "consume_coin": consumed, "recoin": 0,
    }]
    for i, bot in enumerate(PVP_BOTS[:5]):
        rows.append({
            "uid": bot["uid"], "zone": "1-01", "name": bot["name"],
            "vip_lv": int(3 - i // 2),
            "num": max(1, my_num + 12 - i * 3),
            "consume_coin": max(0, consumed + 3000 - i * 500),
            "recoin": 0,
        })
    rows.sort(key=lambda r: r["num"], reverse=True)
    for i, row in enumerate(rows):
        row["rank"] = i + 1
    return {
        "total_num": total, "my_num": my_num, "consume_coin": consumed,
        "recoin": 0, "rank_list": rows,
    }


def _vip_level_from_exp(exp):
    """Highest VIP level whose cumulative requirement is covered by ``exp``.

    ``vip[lv].need_exp`` is the step cost lv -> lv+1, so the requirement to
    reach level L is the sum of steps 1..L-1 (same as the client's
    GlobalFunction.getVipEXP).
    """
    rows = []
    for key, cfg in (_cfg().get("vip") or {}).items():
        try:
            lv = int(key)
            need = int(cfg.get("need_exp", 0) or 0)
        except (TypeError, ValueError, AttributeError):
            continue
        rows.append((lv, need))
    level = 0
    need_total = 0
    for lv, need in sorted(rows):
        if lv <= 0:
            continue
        if exp < need_total:
            break
        level = lv
        need_total += need
    return level


def _altar_activity_open(cfg=None):
    """True while the VIP altar activity window is open."""
    if cfg is None:
        cfg = _cfg().get("ploy_system_simple", {}).get("extract_avatar", {})
    start = cfg.get("start_time")
    end = cfg.get("end_time")
    now = datetime.datetime.utcnow()
    if isinstance(start, datetime.datetime) and now < start:
        return False
    if isinstance(end, datetime.datetime) and now >= end:
        return False
    return True


def _lottery_activity_state(acc):
    """attrs.lottery_activity consumed by PanelCasinoVIP/積分兌換."""
    cfg = _cfg().get("ploy_system_simple", {}).get("extract_avatar", {})
    start = cfg.get("start_time")
    if not isinstance(start, datetime.datetime):
        start = datetime.datetime.utcnow()
    return {
        "score": int(acc.get("lottery_score", 0) or 0),
        "start_time": start,
    }


def _ensure_daily_gift(acc):
    """Reset the daily 30,000 點券 + 1,000,000 金幣 task claim each day."""
    today = datetime.date.today().isoformat()
    if acc.get("everyday_gift_day") != today:
        acc["everyday_gift"] = []
        acc["everyday_gift_day"] = today


def make_user(acc):
    """Shape required by PanelServiceMain.re_user_login()."""
    uid = acc["uid"]
    _ensure_daily_gift(acc)
    # System mail (resource distribution): create the starter mail once and
    # expose the unclaimed count as msg_num for the lobby red dot.
    mailbox = _seed_mailbox(acc)
    unclaimed_mail = sum(1 for m in mailbox.values()
                         if isinstance(m, dict)
                         and int(m.get("status", 0)) != 1)
    # Offline test server: warehouse capacity 2000.  Existing saves are
    # raised in place; the client reads attrs.avatar_len for its cap checks.
    try:
        _cap = int(acc.get("avatar_len", 0))
    except (TypeError, ValueError):
        _cap = 0
    if _cap < 2000:
        acc["avatar_len"] = 2000
    # Starter currencies so the altar / arena / DN are usable immediately.
    if "dn_stone" not in acc:
        acc["dn_stone"] = 200        # enough for the first few DN slots
    if "coin" not in acc:
        acc["coin"] = 500
    if "score" not in acc:
        acc["score"] = 1000
    # 2026-10-25: start with empty soul stores.  The old seed handed every
    # new account three full 英雄戰魂 gauges (2/4/3 souls) and three full
    # 裝備戰魂 gauges, which immediately lit the 神秘商店 red dot on a
    # freshly registered account.  Souls still accrue from duplicates.
    if "avatar_soul" not in acc:
        acc["avatar_soul"] = {}
    if "equip_soul" not in acc:
        acc["equip_soul"] = {}
    # One-time enchant-dust top-up for the four colours (0..3) + light dust.
    # The local server has no dust shop loop worth grinding, so seed enough
    # for testing the enchant caps without changing later login balances.
    if not acc.get("dust_seeded_v2"):
        acc["dust_arr"] = [99999, 99999, 99999, 99999, 99999]
        acc["dust_seeded_v2"] = True
    elif not isinstance(acc.get("dust_arr"), list) or len(acc["dust_arr"]) < 5:
        acc["dust_arr"] = [99999, 99999, 99999, 99999, 99999]
    # Offline convenience: seed cumulative coin spending so the 消費排行
    # milestone rewards can be claimed without a long grind.
    if "spend_coin" not in acc:
        acc["spend_coin"] = 6000
    # 公會研究 (guild research) state: contribution currency, the guild's
    # unlocked skill ids, and the player's personal skill levels.
    if "guild_contribute" not in acc:
        acc["guild_contribute"] = 2000
    if not isinstance(acc.get("guild_graduate_skill"), dict):
        acc["guild_graduate_skill"] = {}
    if not isinstance(acc.get("guild_graduate_skill_list"), list):
        acc["guild_graduate_skill_list"] = []
    # Offline private-server convenience: start at VIP 1 so the VIP tab and
    # 兑换 page always have at least one row to claim/buy.
    if "vip_lv" not in acc:
        acc["vip_lv"] = 1
        acc.setdefault("vip_exp", 0)
    # Guard against stale saves from older config layouts: an unknown cid
    # would hide every chapter tab and PanelCenterPVE.addList_h() would
    # then dereference an empty list.
    cid = acc.get("cid")
    if cid not in PVE_STAGE_ORDER:
        cid = PVE_STAGE_ORDER[0]
    return {
        "uid": uid,
        "sessionid": acc["sessionid"],
        # A non-empty name makes the client skip the scripted tutorial
        # (Game.firstMap -> GuideMaster, which needs server guide data) and go
        # straight to the normal lobby (Game.initUIGroup).
        "name": str(acc.get("nick") or uid),
        # The client reads user.lv, not user.level (PanelTopMain.updateExp).
        # New accounts start at level 25: that is where the remaining module
        # guide triggers (GuideTools.hasDoneGuideType: M11_1/M12_1/M14_1)
        # consider themselves done; we have no guide scripting data, so
        # starting lower makes panels call GuideMaster and crash.
        "lv": int(acc.get("lv", 25)),
        "level": int(acc.get("lv", 25)),
        "exp": int(acc.get("exp", 0)),
        "gold": acc.get("gold", 0),
        "coin": int(acc.get("coin", 0)),
        "score": int(acc.get("score", 0)),
        "diamond": 0,
        # GlobalFunction.getEnergy()/getFragmentPower() treat these as the
        # *timestamp of the last refill* and derive "current energy" from
        # (now - timestamp) / regen.  Send a time far enough in the past that
        # the bar starts full, otherwise PVE refuses to start ("not enough
        # energy").
        "energy": (_ms_dt(acc.get("energy")) if acc.get("energy")
                   else _energy_full_since()),
        "energy_max": 100,
        "fragment_energy": (_ms_dt(acc.get("fragment_energy"))
                            if acc.get("fragment_energy")
                            else _energy_full_since()),
        "vip_lv": int(acc.get("vip_lv", 0)),
        "vip_exp": int(acc.get("vip_exp", 0)),
        "vip_time": (acc.get("vip_time")
                     if isinstance(acc.get("vip_time"), datetime.datetime)
                     else datetime.datetime.utcnow()),
        # gotoOpenActivityPanel() casts user.add_time to Date
        "add_time": datetime.datetime.utcnow(),
        "login_time": datetime.datetime.utcnow(),
        "zone": "1-01",
        "mark": int(acc.get("mark", 0)),
        "medal": int(acc.get("medal", 0)),
        "dn_stone": int(acc.get("dn_stone", 0)),
        # PanelChip reads user.fragment["equips"][fragmentId] as an array of
        # piece slots; getFragmentNumType() counts the positive slots.
        "fragment": {"equips": _ensure_fragments(acc)},
        "exploration": _exploration_state(acc),
        "avatar_soul": acc.get("avatar_soul", {}),
        "equip_soul": acc.get("equip_soul", {}),
        "warriors": [],
        "trade": {},
        "catena": int(acc.get("catena", 0)),
        "random_avatars": [],
        "ploy_cids": dict(acc.get("ploy_cids") or {}),
        "msg_num": unclaimed_mail,
        "apply_num": 0,
        "pf_info": {},
        "attrs": {
            "pvp_rank": int(acc.get("pvp_rank", 300)),
            # 0 makes PanelCenterPVP run its tutorial guide, which needs
            # GuideMaster data we do not ship (#1010), and it injects the
            # broken synthetic "r999999999_6_0" row.  Offline arena always
            # uses the normal bot ladder.
            "pvp_count": int(acc.get("pvp_count") or 1),
            "vip_gift_buy": acc.get("vip_gift_buy", []),
            "vip_gift_buy2": acc.get("vip_gift_buy2", []),
            "pay_first": "",
            "power": 0,
            "dn": acc.get("dn", {}),
            "dn_stone": int(acc.get("dn_stone", 0)),
            "pay_gift": 0,
            "energy_extra": int(acc.get("energy_extra", 0)),
            "fragment_energy": (_ms_dt(acc.get("fragment_energy"))
                                if acc.get("fragment_energy")
                                else _energy_full_since()),
            "fragment_energy_extra": int(acc.get("fragment_energy_extra", 0)),
            # ItemPVEcombat.onTRIGGERED_btn(): avatar count must be below
            # attrs.avatar_len, otherwise it opens the "inventory full" popup
            "avatar_len": int(acc.get("avatar_len", 2000)),
            "friend_len": int(acc.get("friend_len", 50)),
            # 培养 (foster) currency, read by GuideTools.checkCanFosterAvatar
            "culture_book": int(acc.get("culture_book", 0)),
            # 附魔 dust, indexed by LOL_MagicButton colour (PanelEquipMagic).
            "dust": (acc.get("dust_arr")
                     if isinstance(acc.get("dust_arr"), list)
                     else [100, 100, 100, 100, 100]),
            # checkWagerTime() does attrs.wager_free_*.time.  Persisted so
            # the altar's free draw cooldown survives a relogin.  A never-used
            # altar must report an epoch date, not "now", or every fresh
            # account starts with a 10-minute countdown.
            "wager_free_score": _ms_dt_epoch(acc.get("wager_free_score")),
            "wager_free_coin": _ms_dt_epoch(acc.get("wager_free_coin")),
            # PanelCasinoA shows "再抽N次可免費" from this counter.
            "wager_coin_1_count": int(
                acc.get("wager_coin_1_count", 0) or 0),
            # PanelCasinoVIP reads attrs.lottery_activity.score directly.
            "lottery_activity": _lottery_activity_state(acc),
            # Task progress values read by PanelCenterTaskAward.checkTask()
            "login_total": int(acc.get("login_total", 1)),
            "time_consumecoin": int(acc.get("time_consumecoin", 0)),
            "pay_money": 0,
            # PanelActivitySign reads attrs.sign_in.k/.n/.t directly, so this
            # must always exist even before the player's first sign.
            "sign_in": _sign_user_obj(acc),
            # PanelEveryDaySign (月签到) state.
            "check_in": _check_in_state(acc),
            # 公會 (guild) state; 0/-1 when the player is not in a guild.
            "association_id": int(acc.get("guild_id", 0) or 0),
            "association_gold": int(acc.get("guild_gold", 0)),
            "association_lv": int(acc.get("guild_lv", 0)),
            # 公會研究 (PanelGuildBase tab 4 / ItemGuildResearch).
            "guild_contribute": int(acc.get("guild_contribute", 0)),
            "guild_graduate_skill": dict(acc.get("guild_graduate_skill")
                                        or {}),
            # 活動中心轉盤 (PanelActivityRoulette).
            "roulette": _roulette_state(acc),
            # 活動中心福利基金 (PanelActivityFund.checkStatus).
            "fund": _fund_state(acc),
            "fund_add_time": acc["fund_add_time"],
            # 活動中心消費排行 (PanelActivitySpendRank).
            "spend_rank": {"fixed_gift": list(
                acc.get("spend_rank_claimed", []))},
            # 活動中心競猜 attempt counter.
            "gamble_index": int(acc.get("gamble_index", 0)),
            # 活動中心團購 market state flag (used when the event is over).
            "groupon": [0, 0],
            # Talent points: PanelAvatarTalentAvatar indexes attrs.sp[xx].
            "sp": list(_sp_array(acc)),
            # Active talent-reroll session string, null when idle.
            "avatar_talent": (acc.get("avatar_talent")
                              if isinstance(acc.get("avatar_talent"), str)
                              else None),
            # 排位賽 (cross-server PVP).  PanelPVP15 reads server_pvp_cd as a
            # Date and compares it with the current time to enable attacks.
            "server_pvp_cd": _ms_dt(acc.get("server_pvp_cd") or 0),
            "server_pvp_win_count": int(acc.get("server_pvp_win_count", 0)),
            "defensive_squad": _normalize_squad(
                acc.get("defensive_squad")
                or _default_defensive_squad(acc)),
        },
        "records": {
            "current_rank": int(acc.get("pvp_rank", 300)),
            "guide": {},
            "energy_times": int(acc.get("energy_times", 0)),
            # PanelPVEfriend.addList() indexes these by uid to decide whether
            # a helper has already been used today; they must be objects.
            "help_suids": {},
            "help_fuids": {},
            # Daily gift / VIP gift claim indices (PanelCenterTaskAward).
            "everyday_gift": acc.get("everyday_gift", []),
            "vip_gift": acc.get("vip_gift", []),
            # 祭坛 free-draw counter (PanelCenterMain red tag) and the PVP
            # fragment-energy purchase counter (GlobalFunction.sevice_pvp_buy).
            "free_wager_count": int(acc.get("free_wager_count", 0)),
            "fragment_energy_times": int(acc.get("fragment_energy_times", 0)),
            "pvp_buy_count": int(acc.get("pvp_buy_count", 0)),
            "coin_wash_count": int(acc.get("coin_wash_count", 0)),
            # 活動中心福利 free-buy counters (PanelActivityWelfare).
            "welfare_times": list(_welfare_state(acc)["times"]),
            # 活動副本 (PVE tab 3) clear counters / per-battle stage lists.
            "combat_ploy": dict(acc.get("combat_ploy") or {}),
            # 排位賽 remaining attempts (PanelDefenseTeam.fight).
            "server_pvp_num": int(acc.get("server_pvp_num", 10)),
            # PanelActivityExploration.setUIs() indexes these directly.
            "exploration_times": {
                "refresh_count": int(_exploration_state(acc).get("refresh_count", 5)),
                "mode_buy": int(_exploration_state(acc).get("mode_buy", 0)),
                "relive_buy": int(_exploration_state(acc).get("relive_buy", 0)),
                "vip_relive": int(_exploration_state(acc).get("vip_relive", 0)),
            },
        },
        "task": acc.get("task", {}),
        # PVE progress: current normal / hard battle id.  check_pass_battle_main
        # splits "M_011_1" into chapter+stage and decides which chapters show.
        "cid": cid,
        # Hard-mode progress (PanelCenterPVE uses current_battle_main(1)).
        "hid": acc.get("hid") or PVE_STAGE_ORDER[0],
        # GlobalFunction.passBattleInfo() reads combat_score.<tab> as an object;
        # persisted per account so stage stars survive a relogin.
        "combat_score": acc.get("combat_score") or empty_combat_score(),
        # Persistent inventory: stats are derived from cfg.avatar + lv by the
        # client, so material-fed level-ups directly raise combat power.
        "avatars": _ensure_avatars(acc),
        "equips": acc.get("equips") or {},
        # GuideTools.getEquipsNum() iterates my_equips
        "my_equips": _ensure_equips(acc)[0],
        # GlobalFunction.getTeamPower() indexes as_equips[0..4]
        "as_equips": _ensure_equips(acc)[1],
        # GlobalFunction.formateTeamToObj() reads user.team[a][b] for b in 0..4
        "team": _ensure_team(acc),
        "team_num": 1,
    }


def handle(method, params, request):
    """Return the `data` payload for a given service method."""
    accounts = load_accounts()

    if method in ("user.llogin", "user.login", "user.register",
                  "user.default_register"):
        # 2026-10-25: real accounts in Turso (bcrypt hashes).  The AIR client
        # sends the account in session_key and the password in sessionid;
        # web/API callers may use uname/password instead.
        global _CURRENT_ZONE
        account = str(params.get("uname") or params.get("account")
                      or params.get("session_key")
                      or params.get("local_session_key") or "").strip()
        password = str(params.get("password") or params.get("sessionid") or "")
        auto_token = str(params.get("auto_token") or "")
        # Never echo credentials back in the response envelope / logs.
        params.pop("password", None)
        params.pop("sessionid", None)
        params.pop("auto_token", None)
        zone = str(params.get("zone") or "")
        _CURRENT_ZONE = zone or "1-01"
        registering = method in ("user.register", "user.default_register")
        err = _validate_account_name(account)
        if not err and not (auto_token and not registering):
            err = _validate_password(password)
        if err:
            params["register_error" if registering else "login_error"] = err
            return None
        if registering:
            # 2026-10-25: build the complete account (make_user seeds the
            # starter avatars/equips/mailbox) and INSERT it in ONE round trip.
            # The old flow did SELECT + INSERT + UPDATE; on a slow link that
            # could pass the client's socket timeout and show 網路錯誤 even
            # though the account had actually been created.
            acc = new_account(account, "")
            acc["nick"] = str(params.get("nickname") or account)
            acc["sessionid"] = _random_token()
            acc["auto_token"] = _random_token()
            user = make_user(acc)
            try:
                _insert_account(account, password, acc)
            except AccountExistsError:
                # A retried register may hit the row written by an attempt
                # whose reply timed out.  Accept it when the password matches,
                # so the player still sees 註冊成功 and is logged in.
                if not accounts.check_password(account, password):
                    params["register_error"] = "該帳號已存在，請換一個帳號"
                    return None
                acc = accounts.get(account)
                if acc is None:
                    params["register_error"] = "該帳號已存在，請換一個帳號"
                    return None
                user = make_user(acc)
                acc["auto_token"] = _random_token()
                accounts[account] = acc
                user["auto_token"] = str(acc["auto_token"])
                save_accounts(accounts)
                log("    -> register retry ok:", account,
                    "zone=", zone or "1-01")
                return user
            accounts.put_clean(account, acc)
            user["auto_token"] = str(acc["auto_token"])
            log("    -> register ok:", account, "zone=", zone or "1-01")
            return user
        acc = accounts.get(account)
        if acc is None:
            params["login_error"] = "帳號不存在"
            return None
        if auto_token:
            # 2026-10-25: session restore — the client keeps the account
            # and the token issued at the last password login.
            if str(acc.get("auto_token") or "") != auto_token:
                params["login_error"] = "登入已過期，請重新登入"
                return None
        elif not accounts.check_password(account, password):
            # uses the players row already fetched by accounts.get()
            params["login_error"] = "帳號或密碼錯誤"
            return None
        else:
            acc["auto_token"] = _random_token()
        acc["sessionid"] = _random_token()
        # mark dirty so make_user migrations and the new session id
        # are written back by save_accounts()
        accounts[account] = acc
        user = make_user(acc)
        user["auto_token"] = str(acc.get("auto_token") or "")
        save_accounts(accounts)
        log("    -> login ok:", account, "zone=", zone or "1-01")
        return user

    if method == "sys.get_config":
        return {
            "cfg": default_cfg(),
            "cfg_version": "9.1.0",
            "last_login_zone": [],          # GlobalData.$lastLoginZone is an Array
            "recommend_login_zone": "",     # string
            "ana_url": "",
        }

    if method == "sys.get_user_zone":
        return {}

    if method == "user.get_msg":
        # PanelCenterMain.reServiceMsg() walks gift_msg and reads data.length.
        # PanelPVP15's own row opens PanelPVP15Record, which reads
        # data.pvp_msg.server_pvp; each entry's `time` must be a Date.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        recs = []
        pvp_recs = []
        if acc is not None:
            for rec in acc.get("spvp_records", []) or []:
                rec = dict(rec)
                t = rec.get("time")
                if isinstance(t, str):
                    try:
                        rec["time"] = datetime.datetime.fromisoformat(t)
                    except ValueError:
                        rec["time"] = datetime.datetime.utcnow()
                recs.append(rec)
            # Arena (mirror-defense) battle reports for PanelCenterPVP's
            # 戰報 tab.  reServiceMsg reads pvp_msg["pvp"]; without the key
            # it set mMailListArr to undefined and addList #1009'd.
            for rec in acc.get("pvp_records", []) or []:
                rec = dict(rec)
                t = rec.get("time")
                if isinstance(t, str):
                    try:
                        rec["time"] = datetime.datetime.fromisoformat(t)
                    except ValueError:
                        rec["time"] = datetime.datetime.utcnow()
                pvp_recs.append(rec)
        box = {}
        if acc is not None:
            box = _seed_mailbox(acc)
        unclaimed = sum(1 for m in box.values()
                        if isinstance(m, dict)
                        and int(m.get("status", 0)) != 1)
        return {"gift_msg": box, "data": [], "new_num": unclaimed,
                "pvp_msg": {"server_pvp": recs, "pvp": pvp_recs}}

    if method == "user.get_gift_msg":
        # ItemSocialMail index==3 claim button; re_gift_msg() replaces the
        # client's whole inventory/currency state from the reply.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        box = _seed_mailbox(acc)
        gk = str(params.get("gk") or "")
        entry = box.get(gk)
        if not isinstance(entry, dict):
            log("    -> get_gift_msg unknown", gk)
            return _gift_user_payload(acc)
        if int(entry.get("status", 0)) == 0:
            _grant_mail_gift(acc, entry.get("gift_dict") or {})
            entry["status"] = 1
            save_accounts(accounts)
            log("    -> get_gift_msg", gk, entry.get("gift_dict"))
        return _gift_user_payload(acc)

    if method == "user.gm_send_mail":
        # Debug helper: queue arbitrary resources into the in-game mailbox.
        #   user.gm_send_mail {"gift": {...}, "info_type": 99002,
        #                      "info_data": "..."}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        gift = params.get("gift")
        if not isinstance(gift, dict):
            return {}
        mid = _add_mail(
            acc, gift,
            info_type=int(params.get("info_type") or 99002),
            info_data=params.get("info_data") or "")
        save_accounts(accounts)
        log("    -> gm_send_mail", mid, gift)
        return {"id": mid, "gift_msg": _ensure_mailbox(acc)}

    if method == "user.gm_send_mails":
        # Batch helper for the "all heroes / all items" test packages:
        #   {"mails": [{"gift": {...}, "info_type": 99003,
        #              "info_data": "..."}, ...]}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        rows = params.get("mails")
        if not isinstance(rows, list):
            return {}
        ids = []
        for row in rows:
            if not isinstance(row, dict):
                continue
            gift = row.get("gift")
            if not isinstance(gift, dict):
                continue
            ids.append(_add_mail(
                acc, gift,
                info_type=int(row.get("info_type") or 99003),
                info_data=row.get("info_data") or ""))
        save_accounts(accounts)
        log("    -> gm_send_mails", len(ids), "mails")
        return {"ids": ids, "gift_msg": _ensure_mailbox(acc)}

    if method == "user.gm_del_mail":
        # Debug helper: remove one or more queued mails.
        #   user.gm_del_mail {"gks": ["0006", ...]}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        box = _ensure_mailbox(acc)
        gks = params.get("gks")
        if isinstance(gks, str):
            gks = [gks]
        if not isinstance(gks, list):
            gks = []
        removed = []
        for gk in gks:
            if str(gk) in box:
                box.pop(str(gk), None)
                removed.append(str(gk))
        save_accounts(accounts)
        log("    -> gm_del_mail", removed)
        return {"removed": removed, "gift_msg": box}

    if method == "user.get_my_fragments":
        # PanelChip.reFragment() treats data as [ {equips:{fid:[slots]}}, {...} ]
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        frags = _ensure_fragments(acc) if acc is not None else {}
        return [{"equips": frags}, {}]

    if method == "user.compose_fragment":
        # ItemFragment sends {eid}; expects {fragment:{fid:[...]}, get_equips:{...}}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        fid = params.get("eid")
        frags = _ensure_fragments(acc)
        arr = frags.get(fid) if isinstance(fid, str) else None
        if not isinstance(arr, list) or not arr or any(int(v) <= 0 for v in arr):
            return {}
        if fid not in EQUIP_CATALOG:
            return {}
        fid = _final_equip_eid(fid)
        frags[fid] = [0] * len(arr)
        my, _rows = _ensure_equips(acc)
        iid = "e%d" % int(acc.get("next_equip", 1000))
        acc["next_equip"] = int(acc.get("next_equip", 1000)) + 1
        inst = {
            "eid": fid, "lv": 1, "slv": 1, "sexp": 0,
            "new_4attrs": _fixed_equip_attrs(fid),
            "halo": {"lv": 0, "exp": 0},
            "symp": -1, "magic": [0, 0, 0, 0],
        }
        my[iid] = inst
        save_accounts(accounts)
        log("    -> compose_fragment", fid, "->", iid)
        return {"fragment": {fid: [0] * len(arr)},
                "get_equips": {iid: inst}}

    if method == "user.fix_team":
        # Sent by GlobalFunction.changeDNteam() and team edits.  The payload
        # carries both team slots and attrs.dn; persist whichever is present.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        team = params.get("team")
        if isinstance(team, list) and team:
            for _row in team:
                if isinstance(_row, list):
                    _dedupe_team_row(_row)
            acc["team"] = team
        dn = params.get("dn")
        if isinstance(dn, dict):
            acc["dn"] = dn
        save_accounts(accounts)
        log("    -> fix_team team=", len(acc.get("team") or []),
            "dn=", len(acc.get("dn") or {}))
        return make_user(acc)

    if method == "user.dn_unlock":
        # ItemDNavatar.sendService(): open one formation slot.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        key = str(params.get("key") or "")
        nodes = _cfg()["system_simple"]["dn"]
        node = nodes.get(key)
        if not node:
            return {}
        dn = acc.setdefault("dn", {})
        if key in dn:
            return {"dn": dn, "dn_stone": int(acc.get("dn_stone", 0))}
        lv_need = int(node[2])
        stone_need = int(node[3])
        if int(acc.get("lv", 25)) < lv_need:
            return {}
        if int(acc.get("dn_stone", 0)) < stone_need:
            return {}
        acc["dn_stone"] = int(acc.get("dn_stone", 0)) - stone_need
        dn[key] = [0, None, None]
        save_accounts(accounts)
        log("    -> dn_unlock", key, "stone=", acc["dn_stone"])
        return {"dn": dn, "dn_stone": int(acc["dn_stone"])}

    if method == "user.dn_lvup":
        # PanelDetailDN.sendService_lvup(): {key, lv (current)}.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        key = str(params.get("key") or "")
        nodes = _cfg()["system_simple"]["dn"]
        node = nodes.get(key)
        dn = acc.setdefault("dn", {})
        state = dn.get(key)
        if not node or not isinstance(state, list) or len(state) < 2:
            return {}
        try:
            lv = int(params.get("lv") or state[0] or 0)
        except (TypeError, ValueError):
            lv = int(state[0] or 0)
        max_lv = int(_cfg()["system_simple"].get("dn_lv", 10))
        if lv >= max_lv:
            return {}
        cost = lv * lv * int(node[4])
        if int(acc.get("dn_stone", 0)) < cost:
            return {}
        acc["dn_stone"] = int(acc.get("dn_stone", 0)) - cost
        state[0] = lv + 1
        dn[key] = state
        save_accounts(accounts)
        log("    -> dn_lvup", key, "->", state[0], "stone=", acc["dn_stone"])
        return {"dn": dn, "dn_stone": int(acc["dn_stone"])}

    if method == "user.expedition":
        # 2026-10-23: 遠征 = 英雄分解（用戶設計）。派遣的 4★+ 英雄會被
        # 永久消耗（升星材料不返還），獎勵 = 原有魂石 + 活動積分（積分
        # 兌換商店貨幣）。get_avatars 故意留空，客戶端就不會把英雄放回。
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        avatars = _ensure_avatars(acc)
        aids = []
        for key in (params.get("aids") or []):
            if (not isinstance(key, str) or key in aids
                    or key not in avatars):
                continue
            aid = key.split("|")[0]
            if not aid.startswith("A_1"):
                continue
            try:
                star = int(aid.rsplit("_", 1)[1])
            except (ValueError, IndexError):
                continue
            if star < 4:
                continue
            # Team / defense members cannot be dispatched (client locks them).
            if any(key in row for row in (acc.get("team") or [])
                   if isinstance(row, list)):
                continue
            if any(isinstance(node, list) and key in node
                   for node in (acc.get("dn") or {}).values()):
                continue
            aids.append(key)
        if not aids:
            return {}
        points = sum(_expedition_points(k, avatars.get(k)) for k in aids)
        for key in aids:
            del avatars[key]
        _ensure_team(acc)
        now = datetime.datetime.utcnow()
        gain = 5 * DN_STONE_REWARD_RATE * len(aids)
        acc["dn_stone"] = int(acc.get("dn_stone", 0)) + gain
        acc["lottery_score"] = int(acc.get("lottery_score", 0) or 0) + points
        acc["expedition_state"] = {"aids": [], "time": now, "status": 0}
        save_accounts(accounts)
        log("    -> expedition(分解)", aids, "dn_stone+", gain,
            "score+", points, "left", acc["lottery_score"])
        return {
            "dn_stone": int(acc.get("dn_stone", 0)),
            "score": int(acc["lottery_score"]),
            "add_score": points,
            "get_avatars": {},
            "attr_expedition": {
                "aids": [], "time": now, "status": 0,
                "stage": 1, "rewards": [],
            },
        }

    if method in ("user.association_is", "user.associatione_is"):
        # 公會 entry point.  PanelCenterMain calls this when the guild
        # building is tapped; PanelGuildBase branches on data.flag (1 = the
        # player already belongs to a guild, 0 = show the browse/create UI).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        guild_id = int(acc.get("guild_id", 0) or 0)
        worship = {
            "member_worship_user_list": [],
            "member_worship_count": int(acc.get("member_worship_count", 0)),
            "guild_worship_count": int(acc.get("guild_worship_count", 0)),
        }
        user_obj = {
            "association_gold": int(acc.get("guild_gold", 0)),
            "association_lv": int(acc.get("guild_lv", 0)),
            # PanelGuildBase research tab reads these two daily counters.
            "guild_contribute_exchange_normal_count":
                int(acc.get("guild_exchange_normal", 0)),
            "guild_contribute_exchange_expert_count":
                int(acc.get("guild_exchange_expert", 0)),
            "worship_info": worship,
            "guild_worship_count": int(acc.get("guild_worship_count", 0)),
            "member_worship_count": int(acc.get("member_worship_count", 0)),
            "can_guild_worship": True,
            "join_flag": False,
            "exit_flag": False,
        }
        if not guild_id:
            return {"flag": 0, "user": user_obj}
        gid = guild_id
        gname = acc.get("guild_name") or "最強公會"
        gicon = int(acc.get("guild_icon", 0))
        member = {
            "uid": uid, "zone": "1-01",
            "name": str(acc.get("nick") or uid),
            "lv": int(acc.get("lv", 25)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "association_lv": int(acc.get("guild_lv", 0)),
            "power": 0,
            "worship_info": worship,
        }
        info = {
            "id": gid, "name": gname, "level": 1, "icon": gicon,
            "content": "歡迎加入本公會",
            "total_alive": int(acc.get("guild_alive", 0)),
            "member_count": 1, "join_level_limit": 1,
            "association_application": 0, "join_type": 0,
            # Unlocked research skills; the client compares these ids when
            # rendering ItemGuildResearch / ItemResearshSkill.
            "guild_graduate_skill_list": list(
                acc.get("guild_graduate_skill_list") or []),
        }
        return {
            "flag": 1,
            "association_info": info,
            "member_list": [member],
            "user": user_obj,
            "return_code": 0,
        }

    if method == "user.get_association_list":
        # No guilds to browse in the offline world; the empty list makes the
        # client show its "no guild" hint and the 建立/查找 radio tabs.
        return {"info": []}

    if method == "user.add_association":
        # Create the player's own one-member guild.  The client charges the
        # price locally for display but expects the new balances back.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {"res_code": 0}
        name = str(params.get("name") or "").strip() or "最強公會"
        if int(acc.get("guild_id", 0) or 0):
            return {"res_code": -1}
        try:
            pay = int(params.get("flag", 0))
        except (TypeError, ValueError):
            pay = 0
        cost_gold = 1000
        cost_coin = 100
        if pay == 0:
            if int(acc.get("gold", 0)) < cost_gold:
                return {"res_code": 0}
            acc["gold"] = int(acc.get("gold", 0)) - cost_gold
        else:
            if int(acc.get("coin", 0)) < cost_coin:
                return {"res_code": 0}
            acc["coin"] = int(acc.get("coin", 0)) - cost_coin
        acc["guild_id"] = 20001
        acc["guild_name"] = name
        acc["guild_icon"] = int(params.get("icon", 0) or 0)
        acc["guild_gold"] = 0
        acc["guild_lv"] = 0
        save_accounts(accounts)
        log("    -> guild created", name)
        return {
            "res_code": 1,
            "user_dict": {
                "vip_lv": int(acc.get("vip_lv", 0)),
                "vip_exp": int(acc.get("vip_exp", 0)),
                "coin": int(acc.get("coin", 0)),
                "gold": int(acc.get("gold", 0)),
            },
        }

    if method == "user.guild_worship":
        # 公會祈福 (PanelGuildWorship): three tiers, type 0 costs gold and
        # types 1/2 cost coin; each adds guild flourishing/currency.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None or not int(acc.get("guild_id", 0) or 0):
            return {"res_code": -1}
        try:
            wtype = int(params.get("type", 0))
        except (TypeError, ValueError):
            wtype = 0
        cfg = _cfg()["association_simple"]
        tiers = cfg.get("guild_worship") or []
        if wtype < 0 or wtype >= len(tiers):
            return {"res_code": -1}
        times = int(cfg.get("guild_worship_times", 3))
        used = int(acc.get("guild_worship_count", 0))
        if used >= times:
            return {"res_code": -1}
        cost = int(tiers[wtype][0])
        gain = int(tiers[wtype][1])
        currency = "gold" if wtype == 0 else "coin"
        if int(acc.get(currency, 0)) < cost:
            return {"res_code": -1}
        acc[currency] = int(acc.get(currency, 0)) - cost
        acc["guild_gold"] = int(acc.get("guild_gold", 0)) + gain
        acc["guild_alive"] = int(acc.get("guild_alive", 0)) + gain
        acc["guild_worship_count"] = used + 1
        save_accounts(accounts)
        log("    -> guild_worship", wtype, "cost", cost, "gain", gain)
        worship = {
            "member_worship_user_list": [],
            "member_worship_count": int(acc.get("member_worship_count", 0)),
            "guild_worship_count": int(acc["guild_worship_count"]),
        }
        return {
            "res_code": 1,
            "user": {
                "coin": int(acc.get("coin", 0)),
                "gold": int(acc.get("gold", 0)),
                "vip_exp": int(acc.get("vip_exp", 0)),
                "vip_lv": int(acc.get("vip_lv", 0)),
                "association_gold": int(acc.get("guild_gold", 0)),
                "guild_worship_count": int(acc["guild_worship_count"]),
                "worship_info": worship,
            },
            "association": {
                "level": max(1, int(acc.get("guild_lv", 0) or 1)),
                "total_alive": int(acc.get("guild_alive", 0)),
            },
        }

    if method in ("user.get_association_worship_gold_info",
                  "user.get_association_worship_gold"):
        # Member-worship gold pool notifications; no pool is simulated.
        return {"res_code": 1, "gold": 0, "user": {}}

    if method == "user.find_association":
        # Search-by-id tab: only the local guild can ever exist.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid) or {}
        if int(acc.get("guild_id", 0) or 0) != 20001:
            return {"association_info": None}
        return {"association_info": {
            "id": 20001, "name": acc.get("guild_name") or "最強公會",
            "level": 1, "icon": int(acc.get("guild_icon", 0)),
            "content": "歡迎加入本公會",
            "total_alive": int(acc.get("guild_alive", 0)),
            "member_count": 1, "join_level_limit": 1,
            "association_application": 0, "join_type": 0,
        }}

    if method == "user.guild_contribute_exchange":
        # 公會研究 → 貢獻兌換 (PanelGuildUsualTrade / PanelGuildSeniorTrade).
        # type 0 rows cost gold, type 1 rows cost coin.  Daily caps come from
        # guild_contribute_info.exchange_count_info[vip_lv].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None or not int(acc.get("guild_id", 0) or 0):
            return {}
        acc.setdefault("guild_contribute", 2000)
        exchange_id = str(params.get("exchange_id"))
        info_cfg = _cfg()["association_simple"]["guild_contribute_info"]
        row = (info_cfg.get("exchange_cost_info") or {}).get(exchange_id)
        if not isinstance(row, dict):
            return {}
        vip = min(5, max(0, int(acc.get("vip_lv", 0))))
        cap = (info_cfg.get("exchange_count_info") or {}).get(str(vip)) or {}
        expert = int(row.get("type", 0)) == 1
        ckey = "guild_exchange_expert" if expert else "guild_exchange_normal"
        limit = int(cap.get("expert" if expert else "normal", 0))
        used = int(acc.get(ckey, 0))
        if used >= limit:
            return {}
        price = int(row.get("cost", 0))
        kind = "coin" if expert else "gold"
        if int(acc.get(kind, 0)) < price:
            return {}
        acc[kind] = int(acc.get(kind, 0)) - price
        acc[ckey] = used + 1
        gain = int(row.get("contribute", 0))
        acc["guild_contribute"] = int(acc.get("guild_contribute", 0)) + gain
        save_accounts(accounts)
        log("    -> guild exchange", exchange_id, kind, price,
            "contribute+", gain)
        return {
            "coin": int(acc.get("coin", 0)),
            "gold": int(acc.get("gold", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "guild_contribute": int(acc["guild_contribute"]),
        }

    if method == "user.guild_graduate_skill_append":
        # Unlock a research skill for the whole guild (ItemResearshSkill).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        sid = str(params.get("skill_id"))
        gcfg = _cfg()["association_simple"]["guild_graduate"]
        if sid not in (gcfg.get("guild_graduate_skill") or {}):
            return {}
        guild_lv = max(1, int(acc.get("guild_lv", 0) or 1))
        cap = int((gcfg.get("guild_use_skill_count") or {})
                  .get(str(min(10, guild_lv)), 2))
        lst = acc.setdefault("guild_graduate_skill_list", [])
        if sid not in lst and len(lst) >= cap:
            return {}
        if sid not in lst:
            lst.append(sid)
        save_accounts(accounts)
        log("    -> guild skill append", sid, "list", lst)
        return {"guild_graduate_skill_list": lst}

    if method in ("user.guild_graduate_skill_up",
                  "user.guild_graduate_skill_change"):
        # Personal research levels.  Up: spend guild contribution, capped by
        # the guild's level.  Change: swap one studied skill into another at
        # the same level for coin.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        gcfg = _cfg()["association_simple"]["guild_graduate"]
        skills = gcfg.get("guild_graduate_skill") or {}
        acc.setdefault("guild_contribute", 2000)
        learned = acc.setdefault("guild_graduate_skill", {})
        if method == "user.guild_graduate_skill_up":
            sid = str(params.get("skill_id"))
            if sid not in skills:
                return {}
            cur = int(learned.get(sid, 0))
            nxt = cur + 1
            guild_lv = max(1, int(acc.get("guild_lv", 0) or 1))
            if nxt > guild_lv:
                return {}
            levels = skills[sid].get("level") or []
            if nxt >= len(levels) or not isinstance(levels[nxt], dict):
                return {}
            demand = int(levels[nxt].get("up_demand", 0))
            if int(acc.get("guild_contribute", 0)) < demand:
                return {}
            acc["guild_contribute"] = int(acc.get("guild_contribute", 0)) - demand
            learned[sid] = nxt
            save_accounts(accounts)
            log("    -> guild skill up", sid, "lv", nxt, "demand", demand)
            return {"user_data": {
                "guild_graduate_skill": dict(learned),
                "guild_contribute": int(acc["guild_contribute"]),
            }}
        # change
        sid1 = str(params.get("skill_id_1"))
        sid2 = str(params.get("skill_id_2"))
        if sid1 not in skills or sid2 not in skills or sid1 not in learned:
            return {}
        lvl = max(1, int(learned.get(sid1, 1)))
        cost = int((gcfg.get("change_skill_cost") or {})
                   .get(str(lvl), 0))
        if int(acc.get("coin", 0)) < cost:
            return {}
        acc["coin"] = int(acc.get("coin", 0)) - cost
        learned.pop(sid1, None)
        learned[sid2] = max(int(learned.get(sid2, 0)), lvl)
        save_accounts(accounts)
        log("    -> guild skill change", sid1, "->", sid2, "lv", lvl,
            "coin", cost)
        return {"user_data": {
            "coin": int(acc.get("coin", 0)),
            "gold": int(acc.get("gold", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "guild_graduate_skill": dict(learned),
        }}

    if method == "user.association_rank_index":
        # 公會活躍 → 公會排行 (PanelGuildRanking).  Both lists need
        # {name, level, zone, total_alive}; rank text uses zone_rank/all_rank.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid) or {}
        glv = max(1, int(acc.get("guild_lv", 0) or 1))
        own = {
            "id": 20001, "icon": int(acc.get("guild_icon", 0) or 0),
            "name": acc.get("guild_name") or "最強公會",
            "level": glv, "zone": "1-01",
            "member_count": 1,
            "total_alive": int(acc.get("guild_alive", 0)),
        }
        zone_rows = [own]
        all_rows = [own]
        bot_names = ["荒原狼騎", "暗影刺客", "深淵術士", "星界遊俠",
                     "王者侍衛", "雷霆戰神", "永夜君王", "最強王者"]
        for i, name in enumerate(bot_names):
            row = {"id": 30001 + i, "icon": i % 4,
                   "name": name, "level": min(10, 2 + i // 2),
                   "zone": "1-01",
                   "member_count": 10 + i * 3,
                   "total_alive": max(0, 120 - i * 13)}
            zone_rows.append(dict(row))
            all_rows.append(row)
        zone_rows.sort(key=lambda r: r["total_alive"], reverse=True)
        all_rows.sort(key=lambda r: r["total_alive"], reverse=True)
        zone_rank = next((i + 1 for i, r in enumerate(zone_rows)
                          if r["name"] == own["name"]), 1)
        all_rank = next((i + 1 for i, r in enumerate(all_rows)
                         if r["name"] == own["name"]), 1)
        return {
            "res_code": 1,
            "association_info_list": zone_rows,
            "all_association_info_list": all_rows,
            "zone_rank": zone_rank,
            "all_rank": all_rank,
        }

    if method == "user.get_guild_log":
        # 公會日誌 (PanelGuildDay): entries are [Date, String].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid) or {}
        now = datetime.datetime.utcnow()
        name = acc.get("guild_name") or "最強公會"
        return {"res_code": 1, "association_log": [
            [now, "Player 建立了公會 " + name],
            [now - datetime.timedelta(hours=1), "Player 加入公會"],
            [now - datetime.timedelta(hours=2), "公會研究已開啟"],
            [now - datetime.timedelta(hours=3), "公會首領正在等待挑戰"],
        ]}

    if method in ("user.get_associationboss", "user.attack_associationboss",
                  "user.association_reborn", "user.buy_attack_number",
                  "user.get_association_boss_ranks"):
        # 公會首領 (guild boss).  A persistent damage sponge like the world
        # boss: every attack removes 50k HP, consumes one daily free hit,
        # then falls back to coin.  Kills are not simulated, but all of the
        # panel's counters/cooldowns are real and persisted.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {"res_code": -1}
        now = datetime.datetime.utcnow()
        hp_max = 50000000
        hp = int(acc.get("guild_boss_hp", hp_max))
        if hp <= 0:
            hp = hp_max
        kill_num = int(acc.get("guild_boss_kill_num", 0))
        free = int(acc.get("guild_boss_free", 5))
        vip_free = int(acc.get("guild_boss_vip_free", 5))
        next_at = acc.get("guild_boss_attack_at")
        if not isinstance(next_at, datetime.datetime):
            next_at = now
        need_coin = int(_cfg()["association_simple"]["guild_BOSS"]
                        .get("need_coin", 100))

        def _boss_obj():
            return {"kill_num": kill_num, "current_hp": hp,
                    "max_hp": hp_max, "killed_by": 0, "kill_log": None}

        if method == "user.attack_associationboss":
            if free <= 0 and vip_free <= 0:
                if int(acc.get("coin", 0)) < need_coin:
                    return {"res_code": -1}
                acc["coin"] = int(acc.get("coin", 0)) - need_coin
            elif free > 0:
                free -= 1
            else:
                vip_free -= 1
            damage = 50000
            hp = max(1, hp - damage)
            acc["guild_boss_hp"] = hp
            acc["guild_boss_free"] = free
            acc["guild_boss_vip_free"] = vip_free
            acc["guild_boss_attack_at"] = now + datetime.timedelta(seconds=5)
            acc["guild_gold"] = int(acc.get("guild_gold", 0)) + 5
            save_accounts(accounts)
            log("    -> attack_associationboss hp", hp, "free", free)
            return {
                "res_code": 0, "boss": _boss_obj(),
                "attack_log": {"attack_num": 5, "attack_hp": damage,
                               "next_attack_time": acc["guild_boss_attack_at"],
                               "enhance": 0},
                "free_num": free, "vip_free_num": vip_free,
                "attack_hp": damage,
                "vip_lv": int(acc.get("vip_lv", 0)),
                "vip_exp": int(acc.get("vip_exp", 0)),
                "coin": int(acc.get("coin", 0)),
            }

        if method == "user.association_reborn":
            acc["guild_boss_attack_at"] = now
            save_accounts(accounts)
            return {
                "res_code": 0,
                "attack_log": {"attack_num": 5, "attack_hp": 0,
                               "next_attack_time":
                                   now + datetime.timedelta(seconds=2),
                               "enhance": 0},
            }

        if method == "user.buy_attack_number":
            if int(acc.get("coin", 0)) < need_coin:
                return {"res_code": -1,
                        "association_free_num": free,
                        "association_vip_free_num": vip_free}
            acc["coin"] = int(acc.get("coin", 0)) - need_coin
            free += 1
            acc["guild_boss_free"] = free
            save_accounts(accounts)
            return {
                "res_code": 0, "association_free_num": free,
                "association_vip_free_num": vip_free,
                "vip_lv": int(acc.get("vip_lv", 0)),
                "vip_exp": int(acc.get("vip_exp", 0)),
                "coin": int(acc.get("coin", 0)),
            }

        if method == "user.get_association_boss_ranks":
            return {"res_code": 0, "ranks": [], "kill_num": kill_num}

        return {
            "res_code": 0, "boss": _boss_obj(),
            "attack_log": {"attack_num": 5, "attack_hp": 0,
                           "next_attack_time": next_at, "enhance": 0},
            "free_num": free, "vip_free_num": vip_free,
        }

    if method in ("user.assocication_sever_shop_info",
                  "user.assocication_sever_shop_buy",
                  "user.assocication_sever_shop_refresh",
                  "user.assocication_guild_shop_buy"):
        # 公會商店 → 神秘商店 (sever_shop).  The 荣耀 shop is closed by
        # config, so isSever=0 and the client only sends sever_shop_*.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {"res_code": -1}
        shop = _cfg()["association_simple"]["guild_shop"]
        sever = shop.get("sever_shop") or {}
        count = int(acc.get("guild_shop_refresh_count", 0))
        gold_now = int(acc.get("guild_gold", 0))

        if method == "user.assocication_sever_shop_info":
            bought = acc.get("guild_shop_bought") or []
            slots = [{"index": 0, "total_count": 5,
                      "user_count": 1 if i in bought else 0,
                      "can_buy": i not in bought} for i in range(3)]
            return {
                "res_code": 0,
                "sever_shop_info": slots,
                "guild_shop_info": [],
                "guild_shop_refresh_count": count,
                "association_gold": gold_now,
            }

        if method == "user.assocication_sever_shop_buy":
            try:
                idx1 = int(params.get("index_1"))
                idx2 = int(params.get("index_2"))
            except (TypeError, ValueError):
                return {"res_code": -1}
            entries = (sever.get("gift_info") or {}).get(str(idx1)) or []
            if idx2 < 0 or idx2 >= len(entries):
                return {"res_code": -1}
            entry = entries[idx2]
            row = entry[0] if entry and isinstance(entry[0], list) else entry
            if len(row) < 2:
                return {"res_code": -1}
            reward, pay = row[0], row[1]
            need_lv = int(row[2]) if len(row) > 2 else 0
            if need_lv > 1:
                return {"res_code": -1}
            pay_amount = int((pay or {}).get("guild_currency", 0))
            if gold_now < pay_amount:
                return {"res_code": -1, "association_gold": gold_now}
            acc["guild_gold"] = gold_now - pay_amount
            _grant_gift(acc, reward)
            bought = acc.setdefault("guild_shop_bought", [])
            if idx1 not in bought:
                bought.append(idx1)
            save_accounts(accounts)
            log("    -> guild_shop buy", idx1, idx2, "pay", pay_amount)
            user = make_user(acc)
            user.update({"res_code": 1,
                         "association_gold": acc["guild_gold"]})
            return user

        if method == "user.assocication_sever_shop_refresh":
            hand = sever.get("hand_renovate") or [10, 10]
            cost = int(hand[0]) + int(hand[1]) * count
            if gold_now < cost:
                return {"res_code": -1, "association_gold": gold_now}
            acc["guild_gold"] = gold_now - cost
            acc["guild_shop_refresh_count"] = count + 1
            acc["guild_shop_bought"] = []
            save_accounts(accounts)
            log("    -> guild_shop refresh cost", cost)
            return {"res_code": 0,
                    "association_gold": acc["guild_gold"],
                    "guild_shop_refresh_count": count + 1}

        return {"res_code": -1}

    if method in ("user.get_zoneboss", "user.enter_zoneboss"):
        # 遠古大龍 / 世界Boss stub: an always-alive boss so the panel, its
        # team display and the attack loop all work.  HP is tracked per
        # account but the boss never dies, so no end/reward flow is needed.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid) or {}
        now = datetime.datetime.utcnow()
        hp_max = 100000000
        hp = int(acc.get("zone_boss_hp", hp_max))
        if hp <= 0:
            hp = hp_max
        boss = {
            "is_end": 0,
            "add_time": now,
            "end_time": now + datetime.timedelta(hours=24),
            "max_hp": hp_max,
            "current_hp": hp,
            # legacy field names used by some list panels
            "hp": hp,
            "hp_max": hp_max,
            "killed_by": 0,
            "kill_log": None,
            "name": "遠古大龍",
            "lv": 30,
        }
        next_at = acc.get("zone_boss_attack_at")
        if not isinstance(next_at, datetime.datetime):
            next_at = now
        attack_log = {
            "attack_num": int(acc.get("zone_boss_attack_num", 5)),
            "attack_hp": int(acc.get("zone_boss_hurt", 0)),
            "next_attack_time": next_at,
            "enhance": int(acc.get("zone_boss_enhance", 0)),
        }
        return {"is_end": 0, "boss": boss, "attack_log": attack_log,
                "rank_list": [], "report_list": [], "rank": [],
                "mark": int(acc.get("mark", 0)),
                "hurt": int(acc.get("zone_boss_hurt", 0))}

    if method == "user.attack_zoneboss":
        # One attack click: chip 100k HP off the boss, award one medal and
        # start a short cooldown.  Returns the same shape as the poll above
        # plus the fields PanelBossBattle.reService_fight() reads directly.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        now = datetime.datetime.utcnow()
        hp_max = 100000000
        hp = int(acc.get("zone_boss_hp", hp_max))
        if hp <= 0:
            hp = hp_max
        damage = 100000
        hp = max(1, hp - damage)
        acc["zone_boss_hp"] = hp
        acc["zone_boss_hurt"] = int(acc.get("zone_boss_hurt", 0)) + damage
        acc["zone_boss_attack_num"] = int(acc.get("zone_boss_attack_num", 5))
        acc["zone_boss_attack_at"] = now + datetime.timedelta(seconds=5)
        acc["mark"] = int(acc.get("mark", 0)) + 1
        save_accounts(accounts)
        boss = {
            "is_end": 0,
            "add_time": now,
            "end_time": now + datetime.timedelta(hours=24),
            "max_hp": hp_max,
            "current_hp": hp,
            "hp": hp,
            "hp_max": hp_max,
            "killed_by": 0,
            "kill_log": None,
            "name": "遠古大龍",
            "lv": 30,
        }
        attack_log = {
            "attack_num": acc["zone_boss_attack_num"],
            "attack_hp": damage,
            "next_attack_time": acc["zone_boss_attack_at"],
            "enhance": int(acc.get("zone_boss_enhance", 0)),
        }
        return {
            "is_end": 0, "boss": boss, "attack_log": attack_log,
            "rank_list": [], "report_list": [],
            "gold": int(acc.get("gold", 0)),
            "mark": acc["mark"],
            "attack_hp": damage,
            "hurt": acc["zone_boss_hurt"],
            "equip": {}, "kill_gifts": None,
        }

    if method == "user.get_newzone_ranks":
        # 活動中心 → 排行榜: PanelActivityRankList reads data[id] where id is
        # one of rank.gift.rank_sort ([1,2,3]) and each row is
        # [uid, name, vip_lv, value].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid) or {}
        my_lv = int(acc.get("lv", 25))
        my_vip = int(acc.get("vip_lv", 0))
        my_mark = int(acc.get("mark", 0))
        teams = _ensure_team(acc)
        my_power = 0
        for key in teams[0]:
            if key:
                my_power += int(_avatar_power(str(key).split("|")[0], my_lv))
        my_power = int(my_power)
        bots = _pvp_bots_for(acc)[:9]

        def _rank_rows(value_of):
            rows = [[uid, str(acc.get("nick") or uid), my_vip,
                     value_of(None, my_lv, my_power, my_mark)]]
            for i, bot in enumerate(bots):
                rows.append([bot["uid"], bot["name"], int(bot["lv"]) // 10,
                             value_of(bot, int(bot["lv"]),
                                      0, 0)])
            rows.sort(key=lambda r: r[3], reverse=True)
            return rows

        return {
            "1": _rank_rows(lambda b, lv, p, m: lv),
            "2": _rank_rows(lambda b, lv, p, m:
                             int(p if b is None else _team_power(b["team"]))),
            "3": _rank_rows(lambda b, lv, p, m:
                             m if b is None else 10 + b["offset"] * 2),
        }

    if method == "user.get_rank_list":
        # PanelCenterPVP.re_get_rank_list stores data as mPVP_list:
        # [myRank, pkList, enemyList, winnerList, loserList, mark,
        #  dailyRewardBattles].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return [300, [], [], [], [], 0, 0]
        payload = _arena_rank_payload(acc)
        save_accounts(accounts)
        return payload

    if method == "user.refresh_pvp_opponents":
        # 「換一批」: build a new set of arena teams from the hero pools.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return [300, [], [], [], [], 0, 0]
        try:
            acc["pvp_batch"] = int(acc.get("pvp_batch", 0) or 0) + 1
        except (TypeError, ValueError):
            acc["pvp_batch"] = 1
        payload = _arena_rank_payload(acc)
        save_accounts(accounts)
        log("    -> refresh_pvp_opponents batch", acc["pvp_batch"])
        return payload

    # ------------------------------------------------------------------ #
    # 排位賽 / cross-server ranked PVP (PanelPVP15 + PanelDefenseTeam)
    # ------------------------------------------------------------------ #
    if method == "user.get_cross_server_rank_list":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {"my_rank": 0, "rank_list": []}
        my_rank = int(acc.get("server_pvp_rank", 20) or 20)
        avatars = _ensure_avatars(acc)
        aid = next(iter(avatars), "A_6995_5").split("|")[0]
        rows = []
        for bot in _spvp_bots_for(acc):
            rows.append([bot["rank"], bot["zone"], bot["uid"], bot["name"],
                         bot["lv"], 0,
                         bot["teams"][0][0][0], None])
        rows.append([my_rank, "1-01", uid,
                     acc.get("nick") or acc.get("name") or uid,
                     int(acc.get("lv", 25)), int(acc.get("vip_lv", 1)),
                     aid, None])
        rows.sort(key=lambda r: r[0])
        save_accounts(accounts)
        return {"my_rank": my_rank, "rank_list": rows}

    if method == "user.get_cross_server_pvp_rank_info":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return []
        rows = []
        for bot in _spvp_bots_for(acc):
            power = sum(_team_power(t) for t in bot["teams"])
            rows.append([bot["uid"], bot["zone"], bot["rank"], bot["name"],
                         bot["lv"], 0, int(power)])
        squad = acc.get("defensive_squad") or _default_defensive_squad(acc)
        entries = []
        for row in squad:
            for key in row:
                if key:
                    entries.append(key)
        my_entries = _spvp_my_team_entries(acc, entries[:15])
        rows.append([uid, "1-01",
                     int(acc.get("server_pvp_rank", 20) or 20),
                     acc.get("nick") or acc.get("name") or uid,
                     int(acc.get("lv", 25)), int(acc.get("vip_lv", 1)),
                     int(_team_power(my_entries))])
        rows.sort(key=lambda r: r[2])
        return rows

    if method == "user.get_server_pvp_userinfo":
        uid = request.get("uid") or "player"
        acc = accounts.get(uid)
        target = str(params.get("uid") or "")
        if target.startswith("bot_spvp_"):
            bot = _spvp_bot_by_uid(target, acc)
            return {
                "uname": bot["name"],
                "user_lv": bot["lv"],
                "server_pvp_win_count": max(
                    0, int(1000000 / (bot["rank"] + 100))),
                "team_list": _spvp_team_rows(bot["teams"]),
            }
        if acc is None:
            return {}
        squad = acc.get("defensive_squad") or _default_defensive_squad(acc)
        return {
            "uname": acc.get("nick") or acc.get("name") or uid,
            "user_lv": int(acc.get("lv", 25)),
            "server_pvp_win_count": int(acc.get("server_pvp_win_count", 0)),
            "team_list": _spvp_squad_rows(acc, squad),
        }

    if method == "user.get_cross_server_pvp_info":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        bot = _spvp_bot_by_uid(str(params.get("uid") or ""), acc)
        squad = _normalize_squad(
            acc.get("defensive_squad") or _default_defensive_squad(acc))
        # PanelDefenseTeam reads my_attack_squad[t][i][0]; a bare string
        # cell throws #1069 ("Property 0 not found on String").  Empty slots
        # stay "" so the panel treats them as unassigned.
        return {
            "my_attack_squad": squad,
            "team_list": _spvp_team_rows(bot["teams"]),
            "power_list": [int(_team_power(t)) for t in bot["teams"]],
        }

    if method == "user.set_defensive_squad":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        teams = params.get("teams")
        if acc is not None and isinstance(teams, list):
            acc["defensive_squad"] = _normalize_squad(teams)
            save_accounts(accounts)
        return {"res_code": 1}

    if method == "user.set_server_pvp_cd":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        cd = _now_ms() + 10 * 60 * 1000
        if acc is not None:
            acc["server_pvp_cd"] = cd
            save_accounts(accounts)
        return _ms_dt(cd)

    if method == "user.get_server_pvp_playback":
        return {}

    if method == "user.pk_combat_cross_server_pvp":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        bot = _spvp_bot_by_uid(str(params.get("uid") or ""), acc)
        try:
            opp_rank = int(params.get("rank") or bot["rank"])
        except (TypeError, ValueError):
            opp_rank = bot["rank"]
        teams = params.get("teams") or []
        my_rank = int(acc.get("server_pvp_rank", 20) or 20)
        # Fragment energy cost (same currency as the normal arena).
        now_ms = _now_ms()
        left = max(0, _frag_energy_now(acc, now_ms) - 60)
        acc["fragment_energy"] = _frag_energy_stamp(left, now_ms)
        nick = acc.get("nick") or acc.get("name") or uid
        users = {
            "user_a": [uid, "1-01", nick],
            "user_b": [bot["uid"], bot["zone"], bot["name"]],
        }
        combat_res = []
        wins = 0
        for i in range(3):
            mine = _spvp_my_team_entries(
                acc, (teams[i] if i < len(teams) else []) or [])
            bot_team = bot["teams"][i]
            my_power = _team_power(mine)
            enemy_power = _team_power(bot_team)
            # Local server: the first two fields are winnable whenever the
            # player fields a team; the third is a real power check.  This
            # keeps the ladder playable with a small starter roster.
            want_win = bool(mine) and (
                i < 2 or my_power >= enemy_power * 0.75)
            avg_lv = (sum(l for (_a, l) in mine) / len(mine)) if mine else 25
            if want_win:
                # Fewer, lower-level enemies so the client-side simulation
                # matches the server's predicted outcome.
                enemy = [(aid, max(1, int(avg_lv * 0.6)))
                         for (aid, _lv) in bot_team[:3]]
            else:
                enemy = [(aid, max(1, int(avg_lv * 1.25) + 3))
                         for (aid, _lv) in bot_team]
            if want_win:
                wins += 1
            combat_res.append({
                "seed": 2000 + i,
                "Screenings": i + 1,
                "client_orgin_team_a": _spvp_units(mine, 1),
                "client_orgin_team_b": _spvp_units(enemy, 2),
                "users": users,
            })
        final_win = wins >= 2
        old_rank = my_rank
        if final_win:
            if opp_rank < my_rank:
                my_rank = opp_rank
            else:
                my_rank = max(1, my_rank - 1)
            acc["server_pvp_win_count"] = \
                int(acc.get("server_pvp_win_count", 0)) + 1
        else:
            my_rank = min(99999, my_rank + 1)
        acc["server_pvp_rank"] = my_rank
        acc["server_pvp_num"] = max(
            0, int(acc.get("server_pvp_num", 10)) - 1)
        # Rewards (displayed by PanelGameEndAward / setUIInfo_pvp15).
        acc["gold"] = int(acc.get("gold", 0)) + (2000 if final_win else 500)
        acc["coin"] = int(acc.get("coin", 0)) + (50 if final_win else 10)
        acc["dn_stone"] = int(acc.get("dn_stone", 0)) + \
            (20 if final_win else 5) * DN_STONE_REWARD_RATE
        # 2026-10-23: 友情/勝利點數獲取已屏蔽（金幣祭壇改用金幣）。
        grant_exp(acc, 300 if final_win else 80)
        # Record for PanelPVP15Record (user.get_msg -> pvp_msg.server_pvp).
        recs = acc.setdefault("spvp_records", [])
        recs.insert(0, {
            "time": datetime.datetime.utcnow(),
            "data": {
                "rival_uid": bot["uid"], "uname": bot["name"],
                "lv": bot["lv"], "rank": old_rank - my_rank,
                "sign": 1 if final_win else 2,
                "cpb_ids": [], "aid": bot["teams"][0][0][0],
                "morph": None, "zone": bot["zone"], "teams_info": [],
                "my_lv": int(acc.get("lv", 25)),
            },
        })
        acc["spvp_records"] = recs[:20]
        save_accounts(accounts)
        user = make_user(acc)
        log("    -> cross_server_pvp vs", bot["uid"], "wins", wins,
            "rank", old_rank, "->", my_rank)
        return {
            "combat_res": combat_res,
            "users": users,
            "finally_sign": 1 if final_win else 2,
            "current_rank": my_rank,
            "records": {"current_rank": my_rank},
            "server_pvp_num": acc["server_pvp_num"],
            "server_pvp_win_count": acc["server_pvp_win_count"],
            "win_gift": {"gold": 2000 if final_win else 500},
            "gold": int(acc.get("gold", 0)),
            "coin": int(acc.get("coin", 0)),
            "score": int(acc.get("score", 0)),
            "culture_book": int(acc.get("culture_book", 0)),
            "exp": user["exp"],
            "lv": user["lv"],
            "sp": list(_sp_array(acc)),
            "box_key": int(acc.get("box_key", 0)),
            "mark": int(acc.get("mark", 0)),
            "dn_stone": int(acc.get("dn_stone", 0)),
            "dust": user["attrs"]["dust"],
            "medal": int(acc.get("medal", 0)),
            "get_avatars": {},
            "get_avatar_soul": {},
            "get_equips": {},
            "get_equip_soul": {},
            "get_fragments": {},
            "attr_energy_extra": int(acc.get("energy_extra", 0)),
            "attr_fragment_energy": _energy_full_since(),
            "attr_fragment_energy_extra":
                int(acc.get("fragment_energy_extra", 0)),
        }

    if method == "user.pk_combat_pvp":
        # Arena fight against a server bot.  GameMap.initByOrgin() prefers
        # client_orgin_team_* and builds both Avatars from cfg.avatar, so we
        # send those (and omit orgin_team_*, which would only trigger the
        # team-mismatch popup).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        opp_uid = str(params.get("uid") or "")
        bot = _pvp_bot_by_uid(opp_uid, acc)
        try:
            opp_rank = int(params.get("rank") or 0)
        except (TypeError, ValueError):
            opp_rank = 0
        my_rank = int(acc.get("pvp_rank", 300))
        if opp_rank <= 0:
            opp_rank = max(1, my_rank - 1)
        # fragment energy cost (1 per arena fight)
        now_ms = _now_ms()
        left = max(0, _frag_energy_now(acc, now_ms) - 1)
        acc["fragment_energy"] = _frag_energy_stamp(left, now_ms)
        # The client simulates the fight locally and never reports the
        # winner, so predict it from team power and keep rewards conservative
        # when the player is clearly weaker.
        my_units = _pvp_my_units(acc, 1)
        my_power = sum(_avatar_power(u["aid"], u["lv"]) for u in my_units)
        bot_power = _team_power(bot["team"])
        expected_win = my_power >= bot_power * 0.85
        pc = _cfg()["system_simple"]["pvp_config"]
        try:
            full_mark = max(1, int(
                (float(pc[6]) / (opp_rank + float(pc[7]))) ** float(pc[8])
                + float(pc[9])))
        except Exception:                       # noqa: BLE001
            full_mark = 1
        mark_gain = full_mark if expected_win else 1
        # 2026-10-24: arena settlement rewards are displayed x1000.
        mark_reward = mark_gain * 1000
        gold_reward = (100000 if expected_win else 50000) + 30000
        acc["mark"] = int(acc.get("mark", 0)) + mark_reward
        acc["gold"] = int(acc.get("gold", 0)) + gold_reward
        # 2026-10-23: 友情/勝利點數獲取已屏蔽（金幣祭壇改用金幣）。
        acc["medal"] = int(acc.get("medal", 0)) + (1 if expected_win else 0)
        acc["pvp_count"] = int(acc.get("pvp_count", 0)) + 1
        _pvp_daily_count(acc)
        acc["pvp_day_count"] = int(acc.get("pvp_day_count", 0)) + 1
        acc["dn_stone"] = int(acc.get("dn_stone", 0)) + \
            (2 if expected_win else 1) * DN_STONE_REWARD_RATE
        # Beating a higher-ranked opponent takes their slot; otherwise climb
        # one place.  Losses leave the rank unchanged.
        if expected_win:
            if opp_rank < my_rank:
                acc["pvp_rank"] = opp_rank
            else:
                acc["pvp_rank"] = max(1, my_rank - 1)
        # Arena battle report (競技場 > 戰報).  ItemPVPMsg expects a Date in
        # `time` and a `data` object whose numeric keys fill @0/@1/...
        recs = acc.setdefault("pvp_records", [])
        recs.insert(0, {
            "time": datetime.datetime.utcnow(),
            "mtype": 98130,
            "data": {
                "0": bot["name"],
                "1": "勝利" if expected_win else "失敗",
                "2": int(acc.get("pvp_rank", 300)),
                "cpb_id": "",
            },
        })
        acc["pvp_records"] = recs[:20]
        save_accounts(accounts)
        user = make_user(acc)
        log("    -> pk_combat_pvp vs", bot["uid"], "rank", opp_rank,
            "->", acc["pvp_rank"], "power", int(my_power), "/",
            int(bot_power), "win=", expected_win, "mark+", mark_reward,
            "gold+", gold_reward)
        return {
            "seed": 12345,
            # PanelFightAward (shown after a local defeat) reads
            # poke_data.gift_list + poke_gift_index; without them it #1010s.
            # PanelFightAward draws exactly three cards and assigns
            # gift_list[poke_gift_index] to the main card; each list entry
            # must hold a single reward type or _data runs out mid-animation.
            "poke_data": {
                "user_gift": {},
                "gift_list": [
                    {"gold": 100000 if expected_win else 50000},
                    {"mark": mark_reward},
                    {"gold": 30000},
                ],
                "poke_gift_index": 0,
            },
            "sign": 1 if expected_win else 0,
            "def_th": 0,
            "cid": "V_000_0",
            # DoorLayer's VS screen reads these for the 戰力 numbers.
            "my_pr_power": int(my_power),
            "pr_power": int(bot_power),
            "client_orgin_team_a": _pvp_my_units(acc, 1),
            "client_orgin_team_b": _pvp_units(bot["team"], 2),
            "gold": int(acc.get("gold", 0)),
            "coin": int(acc.get("coin", 0)),
            "mark": int(acc.get("mark", 0)),
            "score": int(acc.get("score", 0)),
            "medal": int(acc.get("medal", 0)),
            "culture_book": int(acc.get("culture_book", 0)),
            "dn_stone": int(acc.get("dn_stone", 0)),
            "lv": user["lv"],
            "exp": user["exp"],
            "attrs": user["attrs"],
            "records": user["records"],
            "attr_fragment_energy": user["attrs"]["fragment_energy"],
            "attr_fragment_energy_extra":
                int(acc.get("fragment_energy_extra", 0)),
            "get_avatars": {},
            "get_equips": {},
            "win_gift": {"mark": mark_reward},
        }

    if method == "user.pk_combat":
        # PVE fights are simulated client-side from cfg.combat_main; the
        # response only seeds the RNG.  orgin_team_a/b and server_team_a/b
        # are intentionally absent: GameMap.checkOrginTeam() only traces a
        # warning when they are missing, while present-but-different teams
        # trigger a "combat data mismatch" popup at the end of every fight.
        # (For debugging, sending empty server_team_a/b makes the client POST
        # its full team state to user.pk_combat_errlog.)
        try:
            diff = int(params.get("diff") or 0)
        except (TypeError, ValueError):
            diff = 0
        log("    -> pk_combat", params.get("cid"), "diff=", diff)
        cid = params.get("cid") or PVE_STAGE_ORDER[0]
        nxt = next_stage(cid)
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        gold_now, lv_now, exp_now = 0, 25, 0
        score_now = empty_combat_score()
        drops = {}
        equip_drops = {}
        fragment_drops = {}
        win_gift = {}
        energy_now = _energy_full_since()
        # 活動副本 stages live in cfg.combat_ploy and never move the story
        # cursor (the client would otherwise set cid = next_cid).
        ploy_maps = _activity_combat()
        is_ploy = diff == 2 or cid in ploy_maps
        if is_ploy:
            # The client sends diff=0 for activity stages; force the ploy
            # tab so combat_score.ploy is updated and no story progress moves.
            diff = 2
        if acc is not None:
            stage = (ploy_maps if is_ploy else _combat_main()).get(cid, {})
            if cid in TEST_STAGE_IDS:
                # 傷害測試: zero stamina, no drops, no story progress.  The
                # settlement panel only needs the current wallet values.
                now_ms = _now_ms()
                cur_energy = _energy_now(acc, now_ms)
                acc["energy"] = _energy_stamp(cur_energy, now_ms)
                save_accounts(accounts)
                log("    -> TEST stage", cid, "energy=", cur_energy)
                return {
                    "seed": 12345,
                    "poke_data": {"user_gift": {}},
                    "sign": 1,
                    "gold": int(acc.get("gold", 0)),
                    "lv": int(acc.get("lv", 25)),
                    "exp": int(acc.get("exp", 0)),
                    # Keep the same battle id so GameMap.endFight does not
                    # divert into GuideMaster.initStory() and skip the award.
                    "next_cid": cid,
                    "combat_score": acc.get("combat_score")
                                     or empty_combat_score(),
                    "attr_energy_extra": int(acc.get("energy_extra", 0)),
                    "attr_fragment_energy": 0,
                    "attr_fragment_energy_extra":
                        int(acc.get("fragment_energy_extra", 0)),
                    "energy": _ms_dt(acc["energy"]),
                    "fragment_energy": _energy_full_since(),
                    "combat_star": 3,
                    "dn_stone": int(acc.get("dn_stone", 0)),
                    "get_avatars": {},
                    "get_equips": {},
                    "get_fragments": {},
                    "add_gold": 0,
                    "win_gift": {},
                    "random_av": None,
                }
            # ---- stamina cost -------------------------------------------
            now_ms = _now_ms()
            cost = int(stage.get("energy", 0))
            cur_energy = _energy_now(acc, now_ms)
            left = max(0, cur_energy - cost)
            if cur_energy < cost:
                log("    -> stamina short", cur_energy, "<", cost,
                    "stage", cid, "- allowing the fight anyway")
            acc["energy"] = _energy_stamp(left, now_ms)
            energy_now = _ms_dt(acc["energy"])
            if is_ploy:
                ploy_rec = acc.setdefault("combat_ploy", {})
                first_clear = int(ploy_rec.get(cid, 0)) == 0
                ploy_rec[cid] = int(ploy_rec.get(cid, 0)) + 1
                battle_id = cid.rsplit("_", 1)[0]
                cids = acc.setdefault("ploy_cids", {}).setdefault(
                    battle_id, [])
                if cid not in cids:
                    cids.append(cid)
                # Keep the story cursor where it was.
                nxt = acc.get("cid") or PVE_STAGE_ORDER[0]
            else:
                cleared_key = cid if diff != 1 else cid + "|hard"
                cleared = acc.setdefault("cleared", {})
                first_clear = int(cleared.get(cleared_key, 0)) == 0
                cleared[cleared_key] = int(cleared.get(cleared_key, 0)) + 1
                if diff == 1:
                    acc["hid"] = nxt
                else:
                    acc["cid"] = nxt
            # Gold: first clear x2 and hard mode x2 (the client shows the same
            # two multipliers).  Exp: hard mode x2 only -- 2026-10-25 first
            # clears no longer double exp, so the settlement panel's 經驗+
            # value is exactly what grant_exp receives.
            gold_rate = (2 if first_clear else 1) * (2 if diff == 1 else 1)
            exp_rate = 2 if diff == 1 else 1
            acc["gold"] = int(acc.get("gold", 0)) \
                + int(stage.get("gold", 0)) * gold_rate
            # Energy-trial stages refund stamina instead of dropping gear.
            if stage.get("energy_reward"):
                acc["energy_extra"] = int(acc.get("energy_extra", 0)) \
                    + int(stage["energy_reward"]) * gold_rate
            acc["dn_stone"] = int(acc.get("dn_stone", 0)) \
                + (6 if diff == 1 else 3) * DN_STONE_REWARD_RATE
            lv_now, exp_now = grant_exp(
                acc, int(stage.get("exp", 0)) * exp_rate)
            mark_stage_stars(acc, cid, 3, diff)
            # ---- drops ---------------------------------------------------
            # 2026-10-24: normal/hard story stages drop only wild monsters
            # (+ gold/exp).  Hard final stages also drop one gatekeeper's 5★
            # card.  Activity dungeons keep their original reward mix.
            avatars = _ensure_avatars(acc)
            idx = PVE_STAGE_ORDER.index(cid) if cid in PVE_STAGE_ORDER else 0
            if is_ploy:
                # A_2001_* is the server's internal EXP material and is hidden
                # from the gallery; its icon is a blank circle and opening its
                # detail panel crashes the client.  Drop visible EXP materials
                # instead (武鬥密卷/魔法真諦/真實之書/南瓜/雞腿).
                drop_lv = max(1, min(10, 1 + idx // 2 + (4 if diff else 0)))
                drop_aid = ("A_6996_4", "A_6997_4", "A_6998_4",
                            "A_6992_4", "A_6995_5")[idx % 5]
                slot = int(acc.get("next_slot", 100))
                drop_key = "%s|%d" % (drop_aid, slot)
                acc["next_slot"] = slot + 1
                drop_av = _make_avatar(drop_aid, drop_lv)
                avatars[drop_key] = drop_av
                drops[drop_key] = dict(drop_av)
                drops[drop_key]["i"] = 0
                # A duplicate hero card as the phase-up material.  The client
                # requires the material to have the SAME avatar id as the
                # target (AvatarData.phaseUpList), so rotate three heroes.
                dup_aid = ("A_1001_2", "A_1012_4", "A_1013_3")[idx % 3]
                dup_key = "%s|%d" % (dup_aid, slot + 1)
                acc["next_slot"] = slot + 2
                if dup_aid in _owned_aids(avatars):
                    _note_avatar_soul(acc, dup_aid)
                dup_av = _make_avatar(dup_aid, 1)
                avatars[dup_key] = dup_av
                drops[dup_key] = dict(dup_av)
                drops[dup_key]["i"] = 0
                # 升星材料 (kind-4 avatar) also drops; rarity grows.
                mat_star = max(1, min(5, 1 + idx // 4))
                mat_ids = sorted(mid for mid, meta in AVATAR_CATALOG.items()
                                 if int(meta.get("kind", 1)) == 4
                                 and int(meta.get("star", 1)) == mat_star)
                if mat_ids:
                    mat_aid = mat_ids[idx % len(mat_ids)]
                    mat_slot = int(acc.get("next_slot", 100))
                    acc["next_slot"] = mat_slot + 1
                    mat_key = "%s|%d" % (mat_aid, mat_slot)
                    mat_av = _make_avatar(mat_aid, 1)
                    avatars[mat_key] = mat_av
                    drops[mat_key] = dict(mat_av)
                    drops[mat_key]["i"] = 0
                # 材料試煉 (W_MAT): guaranteed higher-tier material.
                if stage.get("mat_reward"):
                    want_star = int(stage["mat_reward"])
                    extra_ids = sorted(
                        mid for mid, meta in AVATAR_CATALOG.items()
                        if int(meta.get("kind", 1)) == 4
                        and int(meta.get("star", 1)) == want_star)
                    if extra_ids:
                        extra_aid = extra_ids[idx % len(extra_ids)]
                        extra_slot = int(acc.get("next_slot", 100))
                        acc["next_slot"] = extra_slot + 1
                        extra_key = "%s|%d" % (extra_aid, extra_slot)
                        extra_av = _make_avatar(extra_aid, 1)
                        avatars[extra_key] = extra_av
                        drops[extra_key] = dict(extra_av)
                        drops[extra_key]["i"] = 0
                # ---- equipment drop -------------------------------------
                my_equips, _as_equips = _ensure_equips(acc)
                rarity = max(1, min(6, 1 + idx // 3 + (2 if diff else 0)))
                eq_ids = sorted(k for k in EQUIP_CATALOG
                                if len(k.split("_")) == 3
                                and k.split("_")[2] == str(rarity))
                forced_eid = None
                if stage.get("equip_drop"):
                    try:
                        forced_eid = str(stage["equip_drop"][0][0])
                    except (IndexError, TypeError, KeyError):
                        forced_eid = None
                    if forced_eid not in EQUIP_CATALOG:
                        forced_eid = None
                if forced_eid or eq_ids:
                    eid = _final_equip_eid(
                        forced_eid or eq_ids[(idx * 5) % len(eq_ids)])
                    eq_iid = "e%d" % int(acc.get("next_equip", 1000))
                    acc["next_equip"] = int(acc.get("next_equip", 1000)) + 1
                    inst = {
                        "eid": eid, "lv": 1, "slv": 1, "sexp": 0,
                        "new_4attrs": _fixed_equip_attrs(eid),
                        "halo": {"lv": 0, "exp": 0},
                        "symp": -1, "magic": [0, 0, 0, 0],
                    }
                    my_equips[eq_iid] = inst
                    equip_drops[eq_iid] = inst
                    win_gift = {"equip": {eid: 1}}
            else:
                # Story stages: wild monsters only.  Buildings, heroes,
                # equipment, materials and fragments never drop here.
                stage_map = _combat_main().get(cid, {})
                monster_fams = []
                for row in (stage_map.get("team2") or []):
                    fam = str(row[0]).rsplit("_", 1)[0]
                    fam = _PVE_BOSS_FAMILY_MAP.get(fam, fam)
                    if fam in PVE_WILD_MONSTERS and fam not in monster_fams:
                        monster_fams.append(fam)
                if not monster_fams:
                    monster_fams = [
                        PVE_WILD_MONSTERS[idx % len(PVE_WILD_MONSTERS)]]
                drop_count = 2 if cid.endswith("_4") else 1
                # Final stages only field one wild monster, so fill the
                # second drop from the neighbouring wild-monster pool.
                if len(monster_fams) < drop_count:
                    for j in range(len(PVE_WILD_MONSTERS)):
                        fam = PVE_WILD_MONSTERS[
                            (idx + j) % len(PVE_WILD_MONSTERS)]
                        if fam not in monster_fams:
                            monster_fams.append(fam)
                        if len(monster_fams) >= drop_count:
                            break
                for j in range(drop_count):
                    drop_aid = _pve_best_star(
                        monster_fams[j % len(monster_fams)])
                    slot = int(acc.get("next_slot", 100))
                    acc["next_slot"] = slot + 1
                    key = "%s|%d" % (drop_aid, slot)
                    av = _make_avatar(drop_aid, 1)
                    avatars[key] = av
                    drops[key] = dict(av)
                    drops[key]["i"] = 0
                # Hard final: one gatekeeper hero at 5★.
                if diff == 1 and cid.endswith("_4"):
                    gatekeepers = _pve_gatekeepers(_pve_chapter_index(cid))
                    pick = None
                    for fam in gatekeepers:
                        if (fam + "_5") in AVATAR_CATALOG:
                            pick = fam + "_5"
                            break
                    if pick:
                        slot = int(acc.get("next_slot", 100))
                        acc["next_slot"] = slot + 1
                        key = "%s|%d" % (pick, slot)
                        av = _make_avatar(pick, 1)
                        avatars[key] = av
                        drops[key] = dict(av)
                        drops[key]["i"] = 0
            # Activity trials pay 點券 on every clear (stage.win_gift) and
            # never drop avatars/equipment.
            if stage.get("no_drop"):
                for _drop_key in list(drops.keys()):
                    avatars.pop(_drop_key, None)
                drops.clear()
                for _eq_key in list(equip_drops.keys()):
                    my_equips.pop(_eq_key, None)
                equip_drops.clear()
                win_gift = dict(stage.get("win_gift") or {})
            else:
                extra_gift = stage.get("win_gift") or {}
                if extra_gift:
                    win_gift.update(extra_gift)
            if "coin" in win_gift:
                acc["coin"] = int(acc.get("coin", 0)) \
                    + int(win_gift["coin"])
            # Hero/equipment fragment systems are disabled: fragment_drops
            # stays empty for every mode.
            gold_now = acc["gold"]
            score_now = acc.get("combat_score") or empty_combat_score()
            save_accounts(accounts)
            clear_count = int(
                (acc.get("combat_ploy", {}) if is_ploy else cleared).get(
                    cid, 0))
            log("    -> PVE cleared", cid, "x", clear_count,
                "first=", first_clear, "next=", nxt, "ploy=", is_ploy,
                "gold=", gold_now, "lv=", lv_now, "exp=", exp_now,
                "drops=", ",".join(sorted(drops.keys())))
        # The very same object doubles as the battle-award payload: UiLayer
        # dispatches "stage_ui" with the whole pk_combat reply and
        # PanelGameEndAward.setUIInfo() reads .data.gold/.lv/.exp/...
        # Missing fields become undefined and crash PanelTopMain.updateGold().
        return {
            "seed": 12345,
            "poke_data": {"user_gift": {}},
            # PanelGameEndAward treats data.sign == 1 as "victory".  We don't
            # have a server-side battle sim, so assume the player won (the
            # client already plays out and displays the real outcome).
            "sign": 1,
            # ---- reward/result payload ----
            # PanelGameEndAward.setUIInfo uses the combat id to resolve the
            # stage config; sending it keeps the panel safe even if the
            # client clears $tempPVE_combatID (e.g. the PVE list rebuild
            # after 下一關).
            "combat_id": cid,
            "gold": gold_now,
            "coin": int(acc.get("coin", 0)) if acc else 0,
            "lv": lv_now,
            "exp": exp_now,
            "next_cid": nxt,
            "combat_score": score_now,
            "attr_energy_extra": int(acc.get("energy_extra", 0)) if acc else 0,
            "attr_fragment_energy": 0,
            "attr_fragment_energy_extra": 0,
            "energy": energy_now,
            "fragment_energy": _energy_full_since(),
            "combat_star": 3,
            "dn_stone": int(acc.get("dn_stone", 0)) if acc else 0,
            "get_avatars": drops,
            "get_equips": equip_drops,
            "get_fragments": fragment_drops,
            "add_gold": 0,
            "win_gift": win_gift,
            "random_av": None,
        }

    if method == "user.get_pass_battle_gift":
        # Star-progress claim (the 領取 button above PVE/activity stage
        # lists).  normal/hard claim per chapter; activity claims per ploy
        # (W_TRIAL) once all its stages are 3-starred.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        bid = str(params.get("bid") or "")
        try:
            # 2026-10-24: do NOT use `or -1` here — the client sends diff=0
            # for normal stages, and `0 or -1` made every normal chapter
            # claim take the activity branch (need=0 -> reward 0, flag never
            # set, so the 領取 button stayed claimable forever).
            diff = int(params.get("diff", -1))
        except (TypeError, ValueError):
            diff = -1
        cfg = _cfg()
        if diff == -1:
            tab = "ploy"
            meta = (cfg.get("battle_ploy") or {}).get(bid) or {}
            chapter_no = int(meta.get("chapter", 1) or 1)
        else:
            tab = "normal" if diff == 0 else "hard"
            meta = (cfg.get("battle_main") or {}).get(bid) or {}
            try:
                chapter_no = max(
                    1, int(bid.split("_")[1]) - PVE_FIRST_CHAPTER + 1)
            except (IndexError, ValueError):
                chapter_no = 1
        need = int(meta.get("combat", 0) or 0) * 3
        # 2026-10-24 chapter full-star reward:
        #   normal chapter 1 = 1000 點券, +200 per chapter
        #   hard   chapter 1 = 1500 點券, +200 per chapter
        #   activity ploy keeps its own pass_reward (W_TRIAL = 1000).
        if diff == 0:
            reward = 1000 + max(0, chapter_no - 1) * 200
        elif diff == 1:
            reward = 1500 + max(0, chapter_no - 1) * 200
        else:
            reward = int(meta.get("pass_reward", 1000) or 0)
        cs = acc.setdefault("combat_score", empty_combat_score())
        entry = (cs.get(tab) or {}).get(bid)
        got = False
        if isinstance(entry, list) and len(entry) >= 2:
            stars = entry[1] or []
            total = sum(int(s or 0) for s in stars)
            if str(entry[0]) != "1" and need > 0 and total >= need:
                entry[0] = "1"
                acc["coin"] = int(acc.get("coin", 0)) + reward
                got = True
        save_accounts(accounts)
        log("    -> get_pass_battle_gift", bid, "diff", diff,
            "need", need, "reward", reward if got else 0)
        return {
            "coin": int(acc.get("coin", 0)),
            "gold": int(acc.get("gold", 0)),
            "lv": int(acc.get("lv", 25)),
            "exp": int(acc.get("exp", 0)),
            "combat_score": cs,
            "reward": reward if got else 0,
            "get_gift": got,
        }

    if method == "user.pk_combat_errlog":
        # Battle diagnostics pushed by the client when its result disagrees
        # with the server.  Dump everything to the log.
        try:
            log("    -> COMBAT ERRLOG:", json.dumps(
                params, ensure_ascii=False, default=str))
        except Exception as exc:              # noqa: BLE001
            log("    -> COMBAT ERRLOG (unserializable):", exc, params)
        return {}

    if method == "user.online_user":
        # PanelPVEfriend.re_online() stores param1.data and calls .length on
        # it: the handler must return the Array itself (the gateway wraps it
        # in the response's "data" field).  Bots are exempt from the daily-use
        # check (GlobalFunction.check_bot_user looks for "bot" in the uid).
        return [
            _bot_helper("bot_001", "助戰·阿蠻"),
            _bot_helper("bot_002", "助戰·小七", "A_1013_3", 28),
        ]

    if method == "user.get_friends":
        # re_friends() reads .data.friends_list / .data.apply_list
        return {"friends_list": [], "apply_list": []}

    if method in ("user.sell_avatar", "user.sell_avatars"):
        # 軍營 > 出售: PanelSocialMainAvatar.service_sell() sends {aids:[...]}
        # and assigns the reply's data directly to user.gold.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return 0
        avatars = _ensure_avatars(acc)
        protected = set(_ensure_team(acc)[0])
        for val in (acc.get("dn") or {}).values():
            if isinstance(val, list) and len(val) > 1 and isinstance(val[1], str):
                protected.add(val[1])
        total = 0
        sold = []
        for key in params.get("aids") or []:
            if not isinstance(key, str) or key in protected:
                continue
            av = avatars.pop(key, None)
            if av is None:
                continue
            total += _avatar_sell_value(key, av)
            sold.append(key)
        acc["gold"] = int(acc.get("gold", 0)) + total
        save_accounts(accounts)
        log("    -> sell_avatar", len(sold), "gold+", total, "gold=", acc["gold"])
        return int(acc["gold"])

    if method == "user.avatar_culture":
        # 軍營 > 培養.  Charge coin/culture_book, roll pith gains, and keep
        # them pending until the client confirms with ..._save (or discards
        # with ..._cancel).  Response fields are copied directly by
        # PanelAvatarFoster.re_avatar_culture().
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        aid = params.get("aid")
        avatars = _ensure_avatars(acc)
        if not isinstance(aid, str) or aid not in avatars:
            return {}
        type_ = params.get("type") or "coin"
        try:
            num = int(params.get("num") or 1)
        except (TypeError, ValueError):
            num = 1
        if num not in (1, 10):
            num = 1
        price = _cfg()["system_simple"]["culture"].get("price", {})
        cost = int((price.get(type_) or {}).get(str(num), 0))
        if type_ == "coin":
            if int(acc.get("coin", 0)) < cost:
                return {}
            acc["coin"] = int(acc.get("coin", 0)) - cost
        elif type_ == "culture_book":
            if int(acc.get("culture_book", 0)) < cost:
                return {}
            acc["culture_book"] = int(acc.get("culture_book", 0)) - cost
        else:
            return {}
        gains = {}
        for _ in range(num):
            key = random.choice(("hp", "ap", "de_ph", "de_ma"))
            gains[key] = gains.get(key, 0) + random.randint(1, 3)
        acc["culture_pending"] = {"aid": aid, "save_status": gains}
        save_accounts(accounts)
        log("    -> avatar_culture", aid, type_, num, "gains=", gains)
        return {
            "coin": int(acc.get("coin", 0)),
            "culture_book": int(acc.get("culture_book", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "avatar_culture": {"aid": aid, "save_status": gains},
        }

    if method == "user.avatar_culture_save":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        pend = acc.pop("culture_pending", None)
        if not isinstance(pend, dict):
            return {}
        avatars = _ensure_avatars(acc)
        av = avatars.get(pend.get("aid"))
        if av is None:
            save_accounts(accounts)
            return {}
        for key, val in (pend.get("save_status") or {}).items():
            if key in ("hp", "ap", "de_ph", "de_ma"):
                av[key] = int(av.get(key, 0)) + int(val)
        save_accounts(accounts)
        log("    -> avatar_culture_save", pend.get("aid"), av)
        return av

    if method == "user.avatar_culture_cancel":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is not None:
            acc.pop("culture_pending", None)
            save_accounts(accounts)
        return {}

    if method == "user.get_avatar_talent":
        # 角色天賦 roll: pick one config talent for the requested tier and
        # hand the panel a session string.  It parses the tier from
        # split("_")[4] and the id from split("`")[1].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        avatars = _ensure_avatars(acc)
        aid = params.get("aid")
        if not isinstance(aid, str) or aid not in avatars:
            return {}
        try:
            sp_index = int(params.get("sp_index", 0))
        except (TypeError, ValueError):
            sp_index = 0
        tier = sp_index + 2
        cfg = _cfg().get("talent") or {}
        choices = [tid for tid in cfg
                   if len(tid.split("_")) >= 5
                   and tid.split("_")[2] == str(tier)]
        if not choices:
            return {}
        tid = random.choice(choices)
        acc["avatar_talent"] = aid + "`" + tid
        save_accounts(accounts)
        log("    -> get_avatar_talent", aid, tid)
        return {"avatar_talent": acc["avatar_talent"],
                "sp": list(_sp_array(acc))}

    if method == "user.save_talent":
        # Commit or cancel the active talent session.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        session = acc.get("avatar_talent")
        is_save = bool(params.get("is_save"))
        tid = None
        if isinstance(session, str) and "`" in session:
            aid, tid = session.split("`", 1)
            avatars = _ensure_avatars(acc)
            if is_save and aid in avatars:
                avatars[aid]["talent"] = tid
        acc["avatar_talent"] = None
        save_accounts(accounts)
        log("    -> save_talent", "save" if is_save else "cancel", tid)
        if is_save and tid:
            return {"avatar": {"talent": tid}}
        return {}

    if method == "user.phase_up":
        # PanelStarUpStart (isPhaseUp branch) sends {aid: key, aids:[...]} and
        # expects the updated avatar object.  Materials must share the exact
        # same avatar id (AvatarData.phaseUpList); phase_config decides the
        # max phase and the material count.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        avatars = _ensure_avatars(acc)
        key = params.get("aid")
        avatar = avatars.get(key) if isinstance(key, str) else None
        if avatar is None:
            return {}
        aid = key.split("|")[0]
        # 2026-10-21 極限突破: a 6★/7★ hero at the level cap may devour
        # 1-5 眷秘寶 material cards.  Per-card rates:
        #   3★ 靈眷秘寶 10%, 4★ 天眷秘寶 15%, 5★ 神眷秘寶 20%.
        # Rates add up (max 100%).  On success the real level cap rises
        # from 70 to 100 (limit_break=1); on failure the cards are consumed.
        if params.get("mode") == "limit":
            try:
                cur_lv = int(avatar.get("lv", 1))
                count = int(params.get("count") or 1)
            except (TypeError, ValueError):
                cur_lv, count = 1, 1

            def _limit_fail(reason, consumed=()):
                return {"success": False, "count": count, "avatar": avatar,
                        "error": reason, "consumed": list(consumed)}

            if _avatar_star(aid) not in (6, 7):
                return _limit_fail("star")
            if int(avatar.get("limit_break", 0) or 0):
                return _limit_fail("already")
            if cur_lv < 70:
                return _limit_fail("level")
            count = max(1, min(LIMIT_BREAK_MAX_MATS, count))
            # Prefer the exact material cards selected in 吞噬升級.
            selected = params.get("aids")
            if isinstance(selected, list) and selected:
                consumed = [k for k in selected
                            if isinstance(k, str) and k in avatars
                            and k.split("|")[0] in LIMIT_BREAK_RATES]
                if (len(consumed) != len(selected)
                        or len(consumed) != count
                        or len(set(consumed)) != count):
                    return _limit_fail("material")
            else:
                candidates = sorted(
                    (k for k in avatars
                     if isinstance(k, str)
                     and k.split("|")[0] in LIMIT_BREAK_RATES),
                    key=lambda k: -LIMIT_BREAK_RATES[k.split("|")[0]])
                if len(candidates) < count:
                    return _limit_fail("material")
                consumed = candidates[:count]
            rate = min(1.0, sum(LIMIT_BREAK_RATES[k.split("|")[0]]
                                for k in consumed))
            for k in consumed:
                del avatars[k]
            success = random.random() < rate
            if success:
                avatar["limit_break"] = 1
            save_accounts(accounts)
            log("    -> limit_break", key, "count=", count,
                "rate=", rate, "success=", success, "mats=", consumed)
            return {"success": success, "count": count, "rate": rate,
                    "consumed": consumed, "avatar": avatar}
        try:
            type_ = int(aid[2]) if aid[2].isdigit() else 1
        except IndexError:
            type_ = 1
        phases = _cfg()["system_simple"]["phase_config"]
        table = phases[0] if type_ == 1 else phases[1]
        entry = table.get(str(_avatar_star(aid)))
        if not entry:
            return {}
        max_phase = int(entry[1])
        cur_phase = int(avatar.get("phase", 0))
        if cur_phase >= max_phase:
            return {}
        mats = params.get("aids") or []
        if not isinstance(mats, list):
            return {}
        consumed = [k for k in mats
                    if isinstance(k, str) and k != key and k in avatars
                    and k.split("|")[0] == aid]
        need = max(1, int(entry[0]))
        if len(consumed) < need:
            return {}
        for k in consumed:
            del avatars[k]
        avatar["phase"] = cur_phase + 1
        # Each 阶 permanently adds pith (flat stat points) to the hero.
        try:
            pith = int(entry[3]) if len(entry) > 3 else 0
        except (TypeError, ValueError):
            pith = 0
        if pith:
            for fld in ("hp", "ap", "de_ph", "de_ma"):
                avatar[fld] = int(avatar.get(fld, 0) or 0) + pith
        save_accounts(accounts)
        log("    -> phase_up", key, "phase", cur_phase, "->",
            avatar["phase"], "mats=", consumed)
        return avatar

    if method == "user.star_up":
        # PanelStarUpStart.service_starUp() sends {aid: oldKey, aids:[...]}
        # and expects the NEW avatar object as the response data (no wrapper).
        # The client itself computes the new id with getStarUpId() and rewires
        # the team with changeTeamOneToOne(), so we mirror both server-side.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        avatars = _ensure_avatars(acc)
        old_key = params.get("aid")
        old = avatars.get(old_key) if isinstance(old_key, str) else None
        if old is None:
            return {}
        old_aid, _, slot = old_key.partition("|")
        try:
            parts = old_aid.split("_")
            old_star = int(parts[2])
            new_aid = "%s_%s_%d" % (parts[0], parts[1], old_star + 1)
        except (IndexError, ValueError):
            return {}
        # Star-up requires the hero to be at its current level cap
        # (limit-break adds +30 to the 6★ cap).
        old_cfg = _cfg()["avatar"].get(old_aid) or {}
        try:
            old_cap = int((old_cfg.get("tl") or [0, 0, 0, 0, 0])[4] or 0)
        except (IndexError, TypeError, ValueError):
            old_cap = 0
        if int(old.get("limit_break", 0) or 0) > 0:
            old_cap += 30
        if int(old.get("lv", 1) or 1) < old_cap:
            return {}
        # Star-up gates: each current star consumes exactly ONE specific
        # material and requires the phase listed below.
        required_mat = STARUP_MATERIALS.get(old_star)
        if not required_mat:
            return {}
        if int(old.get("phase", 0) or 0) < STARUP_MIN_PHASE.get(old_star, 0):
            return {}
        # 6★ → 7★ requires BOTH 3阶 (满阶) and 極限突破; either one missing
        # blocks the breakthrough.
        if old_star == 6 and int(old.get("limit_break", 0) or 0) <= 0:
            return {}
        new_cfg = _cfg()["avatar"].get(new_aid)
        if not new_cfg:
            return {}
        mats = params.get("aids") or []
        if not isinstance(mats, list):
            return {}
        # Accept exactly one matching material; extra selected avatars are
        # ignored (not consumed) so they cannot be lost by a misclick.
        consumed = [k for k in mats
                    if isinstance(k, str) and k != old_key and k in avatars
                    and k.split("|")[0] == required_mat]
        if not consumed:
            return {}
        consumed = [consumed[0]]
        new_key = new_aid + "|" + slot
        new_av = dict(old)
        new_av["star"] = _avatar_star(new_aid)
        new_av["phase"] = 0
        # Star-up resets the hero to level 1 (pith is preserved).  A new
        # 7★ hero must do its own 極限突破 again to pass level 70.
        new_av["lv"] = 1
        new_av["exp"] = 0
        new_av["limit_break"] = 0
        new_av["tpl"] = _avatar_tpl(new_aid)
        # 2026-10-23: the new card uses the SAME slot as the old one
        # (A_xx_5|2274 -> A_xx_6|2274).  Keeping both in the inventory while
        # _ensure_team() runs made the login slot de-duplication re-key one
        # of them, and the following del avatars[old_key] crashed with
        # KeyError (the client then got an empty reply).  Swap the cards
        # first and rewire the stored team / DN / expedition references by
        # hand, then let _ensure_team() normalise the structure.
        if old_key in avatars:
            del avatars[old_key]
        for key in consumed:
            if key in avatars:
                del avatars[key]
        avatars[new_key] = new_av
        for row in acc.get("team") or []:
            if isinstance(row, list):
                for i, v in enumerate(row):
                    if v == old_key:
                        row[i] = new_key
        for node in (acc.get("dn") or {}).values():
            if isinstance(node, list):
                for i, v in enumerate(node):
                    if v == old_key:
                        node[i] = new_key
        exp_state = acc.get("expedition_state") or {}
        if isinstance(exp_state.get("aids"), list):
            exp_state["aids"] = [new_key if v == old_key else v
                                 for v in exp_state["aids"]]
        team = _ensure_team(acc)
        for i, key in enumerate(team[0]):
            if key == old_key:
                team[0][i] = new_key
        save_accounts(accounts)
        log("    -> star_up", old_key, "->", new_key,
            "mats=", consumed, "lv=", new_av.get("lv"))
        return new_av

    if method == "user.gm_grant_avatar":
        # Local testing helper: add avatar instances and/or gold to the
        # account.  Examples:
        #   user.gm_grant_avatar {aid:"A_6996_4", count:20}
        #   user.gm_grant_avatar {gold:1000000}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        aid = params.get("aid") or ""
        try:
            count = int(params.get("count", 0))
            gold = int(params.get("gold", 0) or 0)
        except (TypeError, ValueError):
            count, gold = 0, 0
        if count < 0 or (count and not isinstance(aid, str)):
            return {}
        avatars = _ensure_avatars(acc)
        slot = int(acc.get("next_slot", 100))
        cap = int(acc.get("avatar_len", 2000))
        room = max(0, cap - len(avatars))
        keys = []
        for i in range(min(count, room)):
            key = "%s|%d" % (aid, slot + i)
            avatars[key] = _new_avatar_instance(aid)
            keys.append(key)
        acc["next_slot"] = slot + len(keys)
        if gold:
            acc["gold"] = int(acc.get("gold", 0)) + gold
        save_accounts(accounts)
        log("    -> gm_grant_avatar", aid, "x", len(keys), "gold+", gold)
        return {"keys": keys, "gold": acc.get("gold"),
                "avatars": {k: avatars[k] for k in keys}}

    if method == "user.gm_grant_equip":
        # Local testing helper: add equipment instances.
        #   user.gm_grant_equip {all:true}      -> every star of every template
        #   user.gm_grant_equip {eids:["E_1001_6"]}
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        eids = params.get("eids")
        if not isinstance(eids, list):
            eids = []
        if params.get("all") or not eids:
            # Short ids only: five-digit sprite ids are display aliases and
            # _ensure_equips() migrates them to the short form anyway.
            eids = sorted(k for k in EQUIP_CATALOG
                          if len(k.split("_")) == 3
                          and k.split("_")[2].isdigit()
                          and len(k.split("_")[2]) == 1)
        my, _rows = _ensure_equips(acc)
        slot = int(acc.get("next_equip", 1000))
        new_eq = {}
        normalized_eids = []
        for eid in eids:
            if not isinstance(eid, str) or eid not in EQUIP_CATALOG:
                continue
            eid = _final_equip_eid(eid)
            if eid not in normalized_eids:
                normalized_eids.append(eid)
        for eid in normalized_eids:
            iid = "e%d" % slot
            slot += 1
            inst = {
                "eid": eid, "lv": 1, "slv": 1, "sexp": 0,
                "new_4attrs": _fixed_equip_attrs(eid),
                "halo": {"lv": 0, "exp": 0},
                "symp": -1, "magic": [0, 0, 0, 0],
                "alchemy": [0, 0],
            }
            my[iid] = inst
            new_eq[iid] = inst
        acc["next_equip"] = slot
        save_accounts(accounts)
        log("    -> gm_grant_equip", len(new_eq), "items")
        return {"new_equips": new_eq, "count": len(new_eq)}

    if method == "user.swallow_avatar":
        # PanelBetterStart.service_swallow() sends
        #   {aid: targetKey, aids: [materialKeys...], gold: cost}
        # and expects {gold: newGold, avatar: updatedTarget}.  It removes the
        # consumed materials from the local user data itself.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        avatars = _ensure_avatars(acc)
        target_key = params.get("aid")
        material_keys = params.get("aids") or []
        target = avatars.get(target_key) if isinstance(target_key, str) else None
        if target is None or not isinstance(material_keys, list):
            return {}
        # 眷秘寶 cards are only consumed through user.phase_up mode:"limit".
        # Return a safe payload instead of an empty response so the client
        # cannot dereference an undefined `data` object.
        if any(isinstance(k, str)
               and k.split("|")[0] in LIMIT_BREAK_RATES
               for k in material_keys):
            return {"gold": int(acc.get("gold", 0)), "avatar": target,
                    "error": "limit_material"}
        consumed = []
        gain = 0
        skill_chance = 0
        love_gain = 0
        for key in material_keys:
            if not isinstance(key, str) or key == target_key:
                continue
            mat = avatars.get(key)
            if mat is None:
                continue
            aid = key.split("|")[0]
            base = aid.rsplit("_", 1)[0]
            # Avatar.isSwallowProtect(): heroes and ordinary 5★+ cards are
            # protected, but the experience crops and the skill/love
            # consumables are explicitly swallowable even at 5★/6★.
            _is_monster_fodder = aid.startswith(("A_2", "A_3", "A_4"))
            if not (base in EXP_CROP_FAMILIES
                    or base in EXP_MATERIAL_FAMILIES
                    or base in SWALLOW_SPECIAL_FAMILIES
                    or _is_monster_fodder):
                continue
            # 2026-10-24: 小怪卡片（含 5★/6★ PVE 掉落）是吞噬肥料，
            # 不再受 5★ 保護，讓「一鍵」可以選取全部小怪。
            if _avatar_star(aid) >= 5 \
                    and not _is_monster_fodder \
                    and base not in EXP_CROP_FAMILIES \
                    and base not in SWALLOW_SPECIAL_FAMILIES:
                continue
            if int(mat.get("morph", 0)) > 0:
                continue
            gain += _avatar_offer_exp(key, mat)
            skill_chance += int(SKILL_UP_CHANCE.get(aid, 0))
            love_gain += int(LOVE_POTION_GAIN.get(aid, 0))
            consumed.append(key)
        if not consumed:
            return {}
        target_aid = target_key.split("|")[0]
        _grant_avatar_exp(target_aid, target, gain)
        if love_gain:
            # 魔法藥水: add 好感度; Avatar.getLoveList() converts it into love
            # levels and lowers the target's 統御值.
            target["love_exp"] = int(target.get("love_exp", 0)) + love_gain
        slv_up = 0
        skill_roll = 0
        if skill_chance:
            # 技能升級材料: each selected cookie contributes its fixed
            # percentage (164=10%, 5★249=20%, 6★249=40%); one roll raises
            # the hero skill by one level, capped at slv_config[0]=10.
            target_pl = ((_cfg()["avatar"].get(target_aid) or {})
                         .get("pl") or [])
            has_skill = len(target_pl) > 10 and bool(target_pl[10])
            slv_cfg = _cfg()["system_simple"].get("slv_config") or [10]
            max_slv = int(slv_cfg[0]) if slv_cfg else 10
            cur_slv = int(target.get("slv", 1))
            skill_roll = min(100, skill_chance)
            if has_skill and cur_slv < max_slv:
                if random.random() * 100.0 < skill_roll:
                    target["slv"] = cur_slv + 1
                    slv_up = 1
        for key in consumed:
            del avatars[key]
        # The client prices every material at its offerExp; mirror that so a
        # forged `gold` field cannot underpay.
        gained_gold = int(acc.get("gold", 0)) - gain
        acc["gold"] = max(0, gained_gold)
        save_accounts(accounts)
        log("    -> swallow", target_key, "<-", consumed,
            "exp+", gain, "lv=", target.get("lv"), "exp=", target.get("exp"),
            "slv=", target.get("slv"), "slvUp=", slv_up,
            "skillChance=", skill_roll,
            "love+", love_gain, "love=", target.get("love_exp", 0),
            "gold=", acc["gold"])
        return {"gold": acc["gold"], "avatar": target}

    if method == "user.equip_dress":
        # Client sends {data: as_equips} and updates its local copy itself;
        # we only need to persist it for the next login.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        data = params.get("data")
        if isinstance(data, list):
            rows = []
            for i in range(5):
                row = data[i] if i < len(data) and isinstance(data[i], list) else []
                row = list(row[:6])
                row += [None] * (6 - len(row))
                rows.append(row)
            acc["as_equips"] = rows
            save_accounts(accounts)
            log("    -> equip_dress saved")
        return {}

    if method == "user.equip_sell":
        # PanelEquipSellSelect expects data = [mark, gold, dust].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        my, rows = _ensure_equips(acc)
        gain_gold = 0
        gain_mark = 0
        souls = acc.setdefault("equip_soul", {})
        dust = acc.get("dust_arr")
        if not isinstance(dust, list) or len(dust) < 5:
            dust = [100, 100, 100, 100, 100]
        for iid in params.get("eqids") or []:
            inst = my.pop(iid, None) if isinstance(iid, str) else None
            if inst is None:
                continue
            eid = inst.get("eid")
            tmpl = EQUIP_CATALOG.get(eid, {})
            gain_gold += int(tmpl.get("gold", 100))
            gain_mark += 1
            # 拆解 also yields one 裝備戰魂 of the same template, plus dust
            # used by 附魔 (five colour buckets).
            if isinstance(eid, str) and eid in EQUIP_CATALOG:
                souls[eid] = int(souls.get(eid, 0)) + 1
                idx = min(4, max(0, _equip_star(eid) - 1))
                dust[idx] = int(dust[idx]) + 5 * _equip_star(eid)
            for row in rows:
                for i, val in enumerate(row):
                    if val == iid:
                        row[i] = None
        acc["dust_arr"] = dust
        acc["gold"] = int(acc.get("gold", 0)) + gain_gold
        acc["mark"] = int(acc.get("mark", 0)) + gain_mark
        save_accounts(accounts)
        log("    -> equip_sell", len(params.get("eqids") or []),
            "gold+", gain_gold, "mark+", gain_mark)
        return [acc["mark"], acc["gold"], dust]

    if method == "user.equip_rise":
        # PanelEquipRise sends {eqid, lv} where `lv` is the equipment's
        # CURRENT level (mCurr_lv = _equip.lv), not an amount.  The panel
        # raises one level per press and expects data = [newLv, gold].
        # Gold follows Equip.getRiseGold(lv):
        #   (equip_config[5] + equip_config[4] * lv^3)
        #       * equipstar_gold[star-1] * equipspace_gold[slot]
        # where slot = {1:0, 2:0, 3:1, 4:2, 5:3}[type].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        my, _rows = _ensure_equips(acc)
        eqid = params.get("eqid")
        inst = my.get(eqid) if isinstance(eqid, str) else None
        if inst is None:
            return {}
        old = int(inst.get("lv", 1))
        eid = str(inst.get("eid") or "")
        star = _equip_effective_star(inst)
        cfg = _cfg()["system_simple"]
        ecfg = cfg.get("equip_config") or [0] * 16
        star_gold = cfg.get("equipstar_gold") or [100] * 10
        space = cfg.get("equipspace_gold") or {}
        # 2026-10-24 rev2: forge cap follows the summoner level, 50 at Lv25
        # rising linearly to 150 at Lv60, then stays 150.  The client mirrors
        # this in GlobalFunction.getEquipRiseMaxLv().
        _alv = int(acc.get("lv", 25))
        if _alv <= 25:
            max_lv = 50
        elif _alv >= 60:
            max_lv = 150
        else:
            max_lv = 50 + (_alv - 25) * 100 // 35
        if old >= max_lv:
            return [old, int(acc.get("gold", 0))]
        try:
            type_ = int(eid[2]) if len(eid) > 2 and eid[2].isdigit() else 1
        except (IndexError, ValueError):
            type_ = 1
        sg = int(star_gold[min(max(star - 1, 0), len(star_gold) - 1)])
        # Mirror Equip.getRiseGold(): type -> {1:0, 2:0, 3:1, 4:2, 5:3},
        # then index the config array.  Keep the legacy dict form working for
        # old saves/config snapshots.
        if isinstance(space, dict):
            space_mul = float(space.get("a%d" % type_, 1) or 1)
        else:
            _idx = {1: 0, 2: 0, 3: 1, 4: 2, 5: 3}.get(type_, 3)
            try:
                space_mul = float(space[_idx])
            except (IndexError, TypeError, ValueError):
                space_mul = 1.0
        cost = int((float(ecfg[5]) + float(ecfg[4]) * old ** 3)
                   * sg * space_mul)
        gold = int(acc.get("gold", 0))
        if gold < cost:
            # Not enough gold: leave the level unchanged; the client's own
            # pre-check normally prevents this path.
            return [old, gold]
        # Forge crit: one attempt can raise +2/+3/+5/+10 levels.  The cost
        # above is still the normal one-level cost (the extra levels are the
        # crit reward), matching the client's one-level price preview.
        gain = 1
        crit = cfg.get("equip_rise_crit") or {}
        if isinstance(crit, dict) and crit:
            roll = random.random()
            cumulative = 0.0
            for key in sorted(crit, key=lambda k: int(k)):
                try:
                    chance = float(crit[key])
                except (TypeError, ValueError):
                    continue
                cumulative += max(0.0, chance)
                if roll < cumulative:
                    try:
                        gain = max(1, int(key))
                    except (TypeError, ValueError):
                        gain = 1
                    break
        new_lv = min(old + gain, max_lv)
        inst["lv"] = new_lv
        acc["gold"] = gold - cost
        save_accounts(accounts)
        log("    -> equip_rise", eqid, old, "->", new_lv, "gain=", gain,
            "cost=", cost, "gold=", acc["gold"])
        return [new_lv, acc["gold"]]

    if method == "user.equip_alchemy":
        # 裝備煉化 (PanelEquipAlchemyStart): consume one duplicate equip of
        # the same template to raise the target's alchemy step.  Response is
        # the full user payload; the panel reads data.my_equips[target].
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        my, rows = _ensure_equips(acc)
        eqids = params.get("eqids") or []
        if not isinstance(eqids, list) or len(eqids) < 2:
            return {}
        tid, sid = str(eqids[0]), str(eqids[1])
        target = my.get(tid)
        stuff = my.get(sid)
        if not isinstance(target, dict) or not isinstance(stuff, dict):
            return {}
        if tid == sid or target.get("eid") != stuff.get("eid"):
            return {}
        if any(sid in row for row in rows):
            return {}
        eid = str(target.get("eid") or "")
        parts = eid.split("_")
        try:
            base_star = int(parts[-1])
        except (TypeError, ValueError):
            return {}
        al = target.get("alchemy")
        if not isinstance(al, list) or len(al) < 2:
            al = [0, 0]
        # 2026-10-21 alchemy redesign: only 6★ equipment is alchemised.
        # Each same-name item advances one stage:
        #   +0 -> +1 -> +2 -> 7★ (alchemy becomes [3, 1]).
        # The final stage changes the displayed star to 7 and Equip.getRes()
        # draws the red frame.  Alchemy adds no combat stats.
        if base_star != 6:
            return {}
        level = int(al[0])
        if level >= 3:
            return {}
        level += 1
        target["alchemy"] = [level, 1 if level >= 3 else 0]
        del my[sid]
        save_accounts(accounts)
        log("    -> equip_alchemy", tid, "level", level, "consume", sid)
        return make_user(acc)

    if method == "user.equip_wash":
        # 洗煉: re-roll the four bonus stats.  Response is [currencyLeft,
        # save_status] where save_status maps attr->delta for the preview.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return [0, {}]
        my, _rows = _ensure_equips(acc)
        eqid = params.get("eqid")
        inst = my.get(eqid) if isinstance(eqid, str) else None
        if inst is None:
            return [int(acc.get("coin", 0)), {}]
        # Remember the last washed item so wash_save can always return a
        # valid instance even when the wash itself changed nothing (already
        # at 255 clicks / insufficient currency).  handle() reloads
        # accounts.json per request, so this must be persisted immediately.
        acc["equip_wash_last"] = eqid
        save_accounts(accounts)
        try:
            num = min(100, max(1, int(params.get("num") or 1)))
        except (TypeError, ValueError):
            num = 1
        ttype = params.get("ttype") or "coin"
        # 2026-10-23: only max-forged (lv 150) gear may be washed.
        try:
            _forge_lv = int(inst.get("lv", 1) or 1)
        except (TypeError, ValueError):
            _forge_lv = 1
        if _forge_lv < 150:
            left = int(acc.get("coin", 0) if ttype == "coin"
                       else acc.get("mark", 0))
            log("    -> equip_wash rejected: forge lv", _forge_lv,
                "< 150", eqid)
            return [left, {}]
        star = _equip_effective_star(inst)
        cfg = _cfg()["system_simple"]["equip_config"]
        # 255-click deterministic wash.  Each click distributes potential
        # proportionally to the present affixes' wash weights, so a fully
        # washed item ends exactly at +2500 hit / +2200 dodge / +22% crit /
        # +75% critdmg / +14% crit resistance.
        base = inst.get("affix_base")
        if not isinstance(base, dict) or not base:
            base = _fixed_equip_attrs(inst.get("eid"))
            inst["affix_base"] = dict(base)
        base = {k: float(base.get(k, 0) or 0) for k in _EQUIP_AFFIX_MAX}
        done = max(0, min(_EQUIP_WASH_CLICKS,
                          int(inst.get("wash_done", 0) or 0)))
        # Remember the state before the first un-saved wash so cancel can
        # restore the halo/potential exactly.
        prev_pending = acc.get("equip_wash_pending")
        if isinstance(prev_pending, dict) and prev_pending.get("eqid") == eqid:
            prev_halo = prev_pending.get("prev_halo") or {
                "lv": int(inst.get("halo", {}).get("lv", 0) or 0),
                "exp": int(inst.get("halo", {}).get("exp", 0) or 0),
            }
            prev_done = int(prev_pending.get("prev_done", done))
        else:
            prev_halo = {
                "lv": int(inst.get("halo", {}).get("lv", 0) or 0),
                "exp": int(inst.get("halo", {}).get("exp", 0) or 0),
            }
            prev_done = done
        if done >= _EQUIP_WASH_CLICKS:
            left = int(acc.get("coin", 0) if ttype == "coin"
                       else acc.get("mark", 0))
            return [left, {}]
        num = min(num, _EQUIP_WASH_CLICKS - done)
        if ttype == "coin":
            cost = (int(cfg[8]) + int(cfg[9]) * star) * num
            if int(acc.get("coin", 0)) < cost:
                return [int(acc.get("coin", 0)), {}]
            acc["coin"] = int(acc.get("coin", 0)) - cost
            left = int(acc["coin"])
        else:
            cost = star * int(cfg[7]) * num
            if int(acc.get("mark", 0)) < cost:
                return [int(acc.get("mark", 0)), {}]
            acc["mark"] = int(acc.get("mark", 0)) - cost
            left = int(acc["mark"])
        cur = {k: float((inst.get("new_4attrs") or {}).get(k, 0) or 0)
               for k in _EQUIP_AFFIX_MAX}
        new_done = done + num
        attrs = dict(base)
        for key, weight in _EQUIP_WASH_MAX.items():
            if base.get(key, 0):
                attrs[key] = round(
                    base[key] + weight * new_done / float(_EQUIP_WASH_CLICKS), 4)
        delta = {k: round(attrs[k] - cur[k], 4) for k in _EQUIP_AFFIX_MAX
                 if abs(attrs[k] - cur[k]) > 1e-9}
        inst["wash_done"] = new_done
        wash_cfg = _cfg()["system_simple"]["equipwash"]
        _equip_add_halo(inst, star, int(wash_cfg[3] if ttype == "coin"
                                        else wash_cfg[2]) * num)
        if new_done >= _EQUIP_WASH_CLICKS:
            # A fully washed item always shows the max (orange) halo; the
            # client's local bar reaches 5级 at this point too, so saving
            # must not drop it back to 4级.
            inst["halo"] = {"lv": int(wash_cfg[5]), "exp": 0}
        acc["equip_wash_pending"] = {
            "eqid": eqid, "attrs": attrs,
            "prev_halo": prev_halo, "prev_done": prev_done,
        }
        save_accounts(accounts)
        log("    -> equip_wash", eqid, ttype, num, "done=", new_done,
            "delta=", delta)
        return [left, delta]

    if method == "user.equip_wash_save":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        pend = acc.pop("equip_wash_pending", None)
        my, _rows = _ensure_equips(acc)
        # re_equip_wash_save() always replaces user.my_equips[mCurr_eid] with
        # param1.data, so ALWAYS return a real instance.  Previously, saving
        # an item whose wash changed nothing (already at 255 clicks or not
        # enough currency) returned {} and the client then crashed in
        # Equip.getRes() (#1009) because the instance lost its eid.
        eqid = pend.get("eqid") if isinstance(pend, dict) \
            else acc.get("equip_wash_last")
        inst = my.get(eqid) if isinstance(eqid, str) else None
        if inst is None:
            return {}
        if isinstance(pend, dict):
            inst["new_4attrs"] = pend.get("attrs") or {}
        save_accounts(accounts)
        log("    -> equip_wash_save", eqid, "pending" if pend else "noop")
        return inst

    if method == "user.equip_wash_cancel":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        inst = None
        if acc is not None:
            pend = acc.pop("equip_wash_pending", None)
            if isinstance(pend, dict):
                my, _rows = _ensure_equips(acc)
                inst = my.get(pend.get("eqid"))
                if isinstance(inst, dict):
                    if isinstance(pend.get("prev_halo"), dict):
                        inst["halo"] = dict(pend["prev_halo"])
                    if "prev_done" in pend:
                        inst["wash_done"] = int(pend["prev_done"])
            save_accounts(accounts)
        return inst or {}

    if method == "user.swallow_skillbook":
        # 參悟: feed type-6 book equips to the selected book, raising slv.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        my, _rows = _ensure_equips(acc)
        eqid = params.get("eqid")
        target = my.get(eqid) if isinstance(eqid, str) else None
        if target is None:
            return {}
        consumed = [k for k in (params.get("eqids") or [])
                    if isinstance(k, str) and k != eqid and k in my
                    and str(my[k].get("eid", "")).startswith("E_6")]
        if not consumed:
            return {}
        cost = 0
        sbc = _cfg()["system_simple"].get("skill_book_exp") or [0] * 10
        try:
            cost = int(target.get("slv", 1)) * _equip_star(target.get("eid")) \
                * int(sbc[5] if len(sbc) > 5 else 0)
        except (TypeError, ValueError):
            cost = 0
        # 2026-10-22 user rule: every consumed book contributes its own
        # level (a LV1 book = +1, a LV4 book = +4), so selecting several
        # books raises the target by several levels.  Capped by
        # slv_config[0] (10).
        try:
            _slv_cap = int((_cfg()["system_simple"].get("slv_config")
                            or [10])[0])
        except (TypeError, ValueError, IndexError):
            _slv_cap = 10
        _slv_cap = max(1, _slv_cap)
        _cur = int(target.get("slv", 1) or 1)
        if _cur >= _slv_cap:
            return {}
        _gain = 0
        for key in consumed:
            try:
                _gain += max(1, int(my[key].get("slv", 1) or 1))
            except (TypeError, ValueError):
                _gain += 1
        for key in consumed:
            del my[key]
        target["slv"] = min(_slv_cap, _cur + _gain)
        acc["gold"] = max(0, int(acc.get("gold", 0)) - cost)
        save_accounts(accounts)
        log("    -> swallow_skillbook", eqid, "slv=", target["slv"],
            "gain=", _gain, "mats=", consumed, "gold=", acc["gold"])
        return {"equip": target, "gold": int(acc["gold"])}

    if method == "user.add_magic":
        # 附魔: spend element dust to roll the equip's symp/magic bonuses.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        my, _rows = _ensure_equips(acc)
        eqid = params.get("eqid")
        inst = my.get(eqid) if isinstance(eqid, str) else None
        if inst is None:
            return {}
        try:
            color = int(params.get("color") or 0)
        except (TypeError, ValueError):
            color = 0
        dust = acc.get("dust_arr")
        if not isinstance(dust, list) or len(dust) < 5:
            dust = [100, 100, 100, 100, 100]
            acc["dust_arr"] = dust
        try:
            cost = int(params.get("dust") or 0)
        except (TypeError, ValueError):
            cost = 0
        if cost <= 0:
            add_cfg = (_cfg()["system_simple"].get("dust") or {}) \
                .get("add_magic") or [[10, 20, 30, 40, 50]]
            row = add_cfg[0] if add_cfg else [10, 20, 30, 40, 50]
            cost = int(row[color % len(row)])
        if int(dust[color % len(dust)]) < cost:
            return inst
        dust[color % len(dust)] = int(dust[color % len(dust)]) - cost
        star = _equip_star(inst.get("eid"))
        slot = color % 4
        magic = inst.get("magic")
        if not isinstance(magic, list) or len(magic) < 4:
            magic = [0, 0, 0, 0]
        else:
            magic = [int(x or 0) for x in magic[:4]]
        cap = 999
        mx = (_cfg()["system_simple"].get("dust") or {}).get("max") or []
        if slot < len(mx):
            try:
                cap = int(mx[slot] or 999)
            except (TypeError, ValueError):
                cap = 999
        # Enchant speed: 3x the old per-click gain, scaled by 0.35 for the
        # 2026-10-25 equipment rebalance (same number of clicks to cap).
        base = max(1, int((20 + 10 * star) * 3 * 0.35))
        gain = random.randint(max(1, base // 2), base)
        magic[slot] = min(cap, magic[slot] + gain)
        inst["magic"] = magic
        # symp marks the last enchanted colour; the client's re_add_magic
        # callback indexes LOL_MagicButton.TXT_SYMP with it, so it must be
        # a valid 0..3 index once an enchant has succeeded.
        inst["symp"] = slot
        save_accounts(accounts)
        log("    -> add_magic", eqid, "color=", color, "dust_left=", dust)
        return inst

    if method == "user.mystery_shop_info":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        s_type = params.get("s_type") or "normal"
        st = _shop_state(acc, s_type)
        save_accounts(accounts)
        return st

    if method == "user.mystery_shop_buy":
        # ItemSoulShop sends {s_type,index,time}; update_UserData() applies
        # new_avatars/new_equips/gold/coin from the reply.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        s_type = params.get("s_type") or "normal"
        st = _shop_state(acc, s_type)
        try:
            idx = int(params.get("index"))
        except (TypeError, ValueError):
            return {}
        bought = st.setdefault("b", [])
        if idx < 0 or idx >= len(st.get("items", [])) or idx in bought:
            return {}
        reward, pay = st["items"][idx]
        pay_type, price = next(iter(pay.items()))
        price = int(price)
        if pay_type == "gold":
            if int(acc.get("gold", 0)) < price:
                return {}
            acc["gold"] = int(acc.get("gold", 0)) - price
        elif pay_type == "coin":
            if int(acc.get("coin", 0)) < price:
                return {}
            acc["coin"] = int(acc.get("coin", 0)) - price
        else:
            return {}
        new_av = {}
        new_eq = {}
        avatars = _ensure_avatars(acc)
        my, _rows = _ensure_equips(acc)
        owned = _owned_aids(avatars)
        for key, val in (reward.get("avatar") or {}).items():
            aid = key.split("|")[0]
            if isinstance(val, dict) and "lv" in val:
                av = val
            elif isinstance(val, (int, float)):
                av = _make_avatar(aid, 1)
            else:
                continue
            if aid in owned:
                _note_avatar_soul(acc, aid)
            owned.add(aid)
            avatars[key] = av
            new_av[key] = av
        for key, val in (reward.get("equip") or {}).items():
            if isinstance(val, dict) and "eid" in val:
                iid, inst = key, val
            elif isinstance(val, (int, float)) and key in EQUIP_CATALOG:
                # Offer stored as {template eid: count}; materialise it now.
                iid = "e%d" % int(acc.get("next_equip", 1000))
                acc["next_equip"] = int(acc.get("next_equip", 1000)) + 1
                key = _final_equip_eid(key)
                inst = {
                    "eid": key, "lv": 1, "slv": 1, "sexp": 0,
                    "new_4attrs": _fixed_equip_attrs(key),
                    "halo": {"lv": 0, "exp": 0},
                    "symp": -1, "magic": [0, 0, 0, 0],
                    # PanelEquipAlchemyStart / Equip.getRes() dereference
                    # alchemy; without it a freshly bought 6★/7★ item kept
                    # the baked 5★ purple frame until the next login.
                    "alchemy": [0, 0],
                }
            else:
                continue
            my[iid] = inst
            new_eq[iid] = inst
        if "gold" in reward:
            acc["gold"] = int(acc.get("gold", 0)) + int(reward["gold"])
        if "coin" in reward:
            acc["coin"] = int(acc.get("coin", 0)) + int(reward["coin"])
        if "dust" in reward:
            # 四色粉塵禮包: add each colour (dust_arr has four colours + light).
            _grant_gift(acc, {"dust": reward["dust"]})
        bought.append(idx)
        save_accounts(accounts)
        log("    -> mystery_shop_buy", s_type, idx, pay_type, price)
        return {
            "gold": int(acc.get("gold", 0)),
            "coin": int(acc.get("coin", 0)),
            "dust": list(acc.get("dust_arr") or [0, 0, 0, 0, 0]),
            "new_avatars": new_av,
            "new_equips": new_eq,
            "b": bought,
        }

    if method == "user.mystery_shop_refresh_by_coin":
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        s_type = params.get("s_type") or "normal"
        cfg = _cfg()["mystery_shop"].get(s_type, {})
        price = int(cfg.get("refresh_price", 0))
        if int(acc.get("coin", 0)) < price:
            return {}
        acc["coin"] = int(acc.get("coin", 0)) - price
        now = _now_ms()
        st = _gen_shop(acc, s_type, now)
        acc.setdefault("mystery_shop", {})[s_type] = st
        save_accounts(accounts)
        log("    -> mystery_shop_refresh", s_type, "coin=", acc["coin"])
        return {"coin": int(acc.get("coin", 0)),
                "vip_exp": 0, "vip_lv": 0,
                "t": st["t"], "b": st["b"], "items": st["items"]}

    if method in ("user.avatar_soul", "user.soul_exchange_avatar"):
        # 英雄戰魂: ItemAvatarSoul sends {aid: <template id>} when the soul
        # gauge is full.  Consume soul_exchange.avatar[star] souls and hand
        # back a fresh duplicate avatar instance (the client then pops the
        # "獲得X" award card).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        aid = params.get("aid")
        if not isinstance(aid, str) or aid not in _cfg()["avatar"]:
            return {}
        star = str(_avatar_star(aid))
        need = int(_cfg()["system_simple"]["soul_exchange"]
                   .get("avatar", {}).get(star, 0) or 0)
        souls = acc.setdefault("avatar_soul", {})
        if need <= 0 or int(souls.get(aid, 0)) < need:
            return {}
        avatars = _ensure_avatars(acc)
        souls[aid] = int(souls.get(aid, 0)) - need
        if souls[aid] <= 0:
            souls.pop(aid, None)
        slot = int(acc.get("next_slot", 100))
        acc["next_slot"] = slot + 1
        new_key = "%s|%d" % (aid, slot)
        avatars[new_key] = _make_avatar(aid, 1)
        save_accounts(accounts)
        log("    -> avatar_soul", aid, "new=", new_key, "left=", souls.get(aid, 0))
        return {"avatars": avatars, "avatar_soul": souls}

    if method in ("user.equip_soul", "user.soul_exchange_equip"):
        # 裝備戰魂: ItemEquipSoul sends {eid: <short template id>}.  Create a
        # new equipment instance once the soul gauge is full.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        eid = params.get("eid")
        if not isinstance(eid, str) or eid not in EQUIP_CATALOG:
            return {}
        eid = _final_equip_eid(eid)
        parts = eid.split("_")
        try:
            star = str(int(parts[2]))
        except (IndexError, ValueError):
            star = "1"
        need = int(_cfg()["system_simple"]["soul_exchange"]
                   .get("equip", {}).get(star, 0) or 0)
        souls = acc.setdefault("equip_soul", {})
        if need <= 0 or int(souls.get(eid, 0)) < need:
            return {}
        my, rows = _ensure_equips(acc)
        souls[eid] = int(souls.get(eid, 0)) - need
        if souls[eid] <= 0:
            souls.pop(eid, None)
        iid = "e%d" % int(acc.get("next_equip", 1000))
        acc["next_equip"] = int(acc.get("next_equip", 1000)) + 1
        my[iid] = {
            "eid": eid, "lv": 1, "slv": 1, "sexp": 0,
            "new_4attrs": _fixed_equip_attrs(eid),
            "halo": {"lv": 0, "exp": 0},
            "symp": -1, "magic": [0, 0, 0, 0],
        }
        save_accounts(accounts)
        log("    -> equip_soul", eid, "new=", iid, "left=", souls.get(eid, 0))
        return {"my_equips": my, "as_equips": rows, "equip_soul": souls}

    if method == "user.check_in":
        # 月簽到 (PanelEveryDaySign).  Claims the current day's reward and,
        # for VIPs, optionally the doubled one.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        st = _check_in_state(acc)
        cfg = _cfg()["check_in"].get(str(st.get("m", 1))) or []
        if not cfg:
            return {}
        hc = st.setdefault("had_check", [0, 0])
        n = int(st.get("n", 0))
        idx = min(max(0, n), len(cfg) - 1)
        want_vip = bool(params.get("is_vip"))
        if want_vip:
            if not (int(hc[0]) == 1 and int(hc[1]) == 0):
                return {}
            _grant_gift(acc, cfg[idx].get("reward") or {})
            st["had_check"] = [1, 1]
            st["n"] = n + 1
        else:
            if int(hc[0]) == 1:
                return {}
            _grant_gift(acc, cfg[idx].get("reward") or {})
            hc[0] = 1
            if int(cfg[idx].get("vip_double") or 0) <= 0:
                # 2026-10-24 fix: keep the "claimed today" flag.  Resetting
                # it to [0,0] let the player re-open the panel and claim the
                # same day's reward repeatedly.
                st["had_check"] = [1, 1]
                st["n"] = n + 1
        save_accounts(accounts)
        log("    -> check_in", st.get("m"), "n=", st.get("n"),
            "vip=", want_vip, "reward=", cfg[idx].get("reward"))
        user = make_user(acc)
        user["check_in"] = user["attrs"]["check_in"]
        return user

    if method in ("user.vip_gift", "user.vip_gift_buy"):
        # VIP 免费等级礼包 (user.vip_gift, granted from the task centre) and
        # VIP 兑换页购买 (user.vip_gift_buy: type 0 = level gift claim,
        # type 1 = coin purchase).  Both responses are copied field-by-field
        # by ItemTaskAward.reFun / ItemVIPShopping.re_buy.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        try:
            vip_lv = int(params.get("gnum") if method == "user.vip_gift"
                         else params.get("vip_lv"))
        except (TypeError, ValueError):
            return {}
        vip_cfg = _cfg()["vip"].get(str(vip_lv))
        if not vip_cfg:
            return {}
        if method == "user.vip_gift":
            claimed = acc.setdefault("vip_gift", [])
            if vip_lv in claimed or vip_lv > int(acc.get("vip_lv", 0)):
                return make_user(acc)
            for gift in vip_cfg.get("gift") or []:
                _grant_gift(acc, gift)
            claimed.append(vip_lv)
            save_accounts(accounts)
            log("    -> vip_gift", vip_lv)
            return make_user(acc)

        try:
            typ = int(params.get("type") or 0)
        except (TypeError, ValueError):
            typ = 0
        cur_lv = int(acc.get("vip_lv", 0))
        if typ == 1:
            claimed = acc.setdefault("vip_gift_buy2", [])
            base = vip_cfg.get("gift_coin_buy") or {}
            price = int((base.get("pay") or [0, 0])[1])
            if vip_lv in claimed or vip_lv > cur_lv:
                return {}
            if int(acc.get("coin", 0)) < price:
                return {}
            acc["coin"] = int(acc.get("coin", 0)) - price
            _grant_gift(acc, base.get("data") or {})
            claimed.append(vip_lv)
        else:
            claimed = acc.setdefault("vip_gift_buy", [])
            base = vip_cfg.get("gift_buy") or {}
            if vip_lv in claimed or vip_lv > cur_lv:
                return {}
            _grant_gift(acc, base.get("data") or {})
            claimed.append(vip_lv)
        save_accounts(accounts)
        log("    -> vip_gift_buy lv", vip_lv, "type", typ)
        user = make_user(acc)
        user.update({
            "attr_energy_extra": int(user["attrs"].get("energy_extra", 0)),
            "vip_gift_buy": acc.get("vip_gift_buy", []),
            "vip_gift_buy2": acc.get("vip_gift_buy2", []),
            "dust": user["attrs"].get("dust"),
            "box_key": int(acc.get("box_key", 0)),
        })
        return user

    if method == "user.sign_in":
        # Daily sign: n+1 of sign_in[k].num.  One per calendar day; the
        # response is copied wholesale into GlobalData.$userData.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        k, n, t = _sign_state(acc)
        entry = _sign_cfg().get(str(k)) or {}
        num = int(entry.get("num", 0))
        today = datetime.datetime.now().date()
        already = False
        if t:
            already = datetime.datetime.fromtimestamp(t / 1000.0).date() == today
        if n >= num or num <= 0 or already:
            log("    -> sign_in ignored k=", k, "n=", n, "num=", num,
                "already=", already)
            return _sign_response(acc)
        st = acc.setdefault("sign_in", {})
        st["n"] = min(num, n + 1)
        st["t"] = _now_ms()
        save_accounts(accounts)
        log("    -> sign_in k=", k, "n=", st["n"], "/", num)
        return _sign_response(acc)

    if method == "user.sign_reward":
        # Full-round reward, then advance to the next sign_in round.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        k, n, t = _sign_state(acc)
        entry = _sign_cfg().get(str(k)) or {}
        num = int(entry.get("num", 0))
        if num <= 0 or n < num:
            log("    -> sign_reward ignored k=", k, "n=", n, "num=", num)
            return _sign_response(acc)
        gift = entry.get("reward") or entry.get("gift") or {}
        _grant_gift(acc, gift)
        keys = sorted(int(x) for x in _sign_cfg()
                      if str(x).lstrip("-").isdigit())
        next_k = 0
        for key in keys:
            if key > k:
                next_k = key
                break
        st = acc.setdefault("sign_in", {})
        st["k"], st["n"], st["t"] = next_k, 0, t
        save_accounts(accounts)
        log("    -> sign_reward k=", k, "->", next_k, "gift=", gift)
        return _sign_response(acc, gift)

    if method == "user.full_energy":
        # Buy a full PVE stamina bar with coin (PanelService shop / the
        # "no stamina" popup both go through GlobalFunction.service_energy).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        ec = _cfg()["system_simple"]["energy_config"]
        times = int(acc.get("energy_times", 0))
        if times >= int(ec[5]):
            log("    -> full_energy rejected: purchase cap", times)
            return {}
        cost = int(ec[4]) + times * int(ec[7])
        if int(acc.get("coin", 0)) < cost:
            log("    -> full_energy rejected: coin", acc.get("coin", 0),
                "<", cost)
            return {}
        now_ms = _now_ms()
        acc["coin"] = int(acc.get("coin", 0)) - cost
        acc["energy_times"] = times + 1
        acc["energy"] = _energy_stamp(_energy_max(acc), now_ms)
        save_accounts(accounts)
        log("    -> full_energy #", times + 1, "coin=", acc["coin"])
        return {
            "attr_energy_extra": int(acc.get("energy_extra", 0)),
            "energy_times": acc["energy_times"],
            "energy": _ms_dt(acc["energy"]),
            "coin": int(acc["coin"]),
        }

    if method == "user.full_fragment_energy":
        # PVP fragment-energy refill (GlobalFunction.sevice_pvp_buy).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cc = _cfg()["system_simple"]["capacity_config"]
        times = int(acc.get("fragment_energy_times", 0))
        if times >= int(cc[4]):
            log("    -> full_fragment_energy rejected: cap", times)
            return {}
        cost = int(cc[6]) + times * int(cc[5])
        if int(acc.get("coin", 0)) < cost:
            log("    -> full_fragment_energy rejected: coin",
                acc.get("coin", 0), "<", cost)
            return {}
        now_ms = _now_ms()
        acc["coin"] = int(acc.get("coin", 0)) - cost
        acc["fragment_energy_times"] = times + 1
        acc["fragment_energy"] = _frag_energy_stamp(_frag_energy_max(acc),
                                                    now_ms)
        save_accounts(accounts)
        log("    -> full_fragment_energy #", times + 1, "coin=", acc["coin"])
        return {
            "attr_fragment_energy_extra":
                int(acc.get("fragment_energy_extra", 0)),
            "fragment_energy_times": acc["fragment_energy_times"],
            "fragment_energy": _ms_dt(acc["fragment_energy"]),
            "coin": int(acc["coin"]),
        }

    if method in ("user.expand_avatar_len", "user.expand_friend_len"):
        # 商城 → 商店 → 英雄/好友容量扩充.  The client increments its own
        # attrs locally and only needs the server to persist the new cap and
        # deduct the coin.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        key = "avatar_len" if method == "user.expand_avatar_len" \
            else "friend_len"
        cfg = _cfg()["system_simple"][key]
        inc = int(cfg[1])
        cost = int(cfg[2])
        # cfg[3] is the client's purchase window (relative to the VIP
        # bonus), not an absolute cap; the client blocks over-buying, so the
        # server only needs a sane upper bound.
        cap = 9999
        cur = int(acc.get(key, int(cfg[0])))
        if inc <= 0 or cur + inc > cap:
            log("    ->", method, "rejected: cap", cur, "/", cap)
            return {}
        if int(acc.get("coin", 0)) < cost:
            log("    ->", method, "rejected: coin", acc.get("coin", 0),
                "<", cost)
            return {}
        acc["coin"] = int(acc.get("coin", 0)) - cost
        acc[key] = cur + inc
        save_accounts(accounts)
        log("    ->", method, cur, "->", acc[key], "coin=", acc["coin"])
        return {key: acc[key], "coin": int(acc["coin"])}

    if method in ("user.roulette", "user.roulette_lottery"):
        # 活動中心 → 轉盤: one free single spin per day, otherwise coin *
        # num.  Rewards come from roulette.random_gift["6"]; milestone
        # rewards from roulette.fixed_gift are claimed via _lottery.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["roulette"]
        st = _roulette_state(acc)

        if method == "user.roulette":
            try:
                num = int(params.get("num") or 1)
            except (TypeError, ValueError):
                num = 1
            if num not in (1, 10):
                num = 1
            today = datetime.date.today().isoformat()
            is_free = acc.get("roulette_last_day") != today
            cost = 0 if (is_free and num == 1) else int(cfg["coin"]) * num
            if int(acc.get("coin", 0)) < cost:
                return {}
            acc["coin"] = int(acc.get("coin", 0)) - cost
            pool = (cfg.get("random_gift") or {}).get("6") or []
            if not pool:
                return {}
            gift_list = []
            for _ in range(num):
                entry = random.choice(pool)
                reward = entry[0] if isinstance(entry, list) else entry
                if isinstance(reward, dict):
                    _grant_gift(acc, reward)
                    gift_list.append(reward)
            st["fixed_count"] = int(st.get("fixed_count", 0)) + len(gift_list)
            st["last_time"] = datetime.datetime.utcnow()
            acc["roulette_last_day"] = today
            save_accounts(accounts)
            log("    -> roulette", num, "cost", cost,
                "rewards", len(gift_list))
            user = make_user(acc)
            user.update({
                "attr_roulette": st,
                "sp": list(_sp_array(acc)),
                "gift_list": gift_list,
                "radio_gift": [],
                "get_avatars": {}, "get_equips": {},
                "culture_book": int(acc.get("culture_book", 0)),
                "dust": user["attrs"].get("dust"),
                "box_key": int(acc.get("box_key", 0)),
            })
            return user

        # Milestone reward claim (level = required spin count).
        try:
            level = int(params.get("level") or 0)
        except (TypeError, ValueError):
            return {}
        rewards = (cfg.get("fixed_gift") or {}).get(str(level))
        claimed = acc.setdefault("roulette_claimed", [])
        if (not isinstance(rewards, dict)
                or level in claimed
                or int(st.get("fixed_count", 0)) < level):
            return {}
        _grant_gift(acc, rewards)
        claimed.append(level)
        fd = st.setdefault("fixed_draw", {})
        fd[str(level)] = int(fd.get(str(level), 0)) + 1
        save_accounts(accounts)
        log("    -> roulette_lottery level", level, "reward", rewards)
        user = make_user(acc)
        user.update({
            "attr_roulette": st,
            "sp": list(_sp_array(acc)),
            "culture_book": int(acc.get("culture_book", 0)),
        })
        return user

    if method == "user.fund":
        # 活動中心 → 福利基金 daily return claim (PanelActivityFund).
        # The client only needs `data` (new coin balance) and `server_now`;
        # it stores the latter as attrs.fund.last_time.  Payout mirrors
        # checkStatus(): claim only inside the post-buy window, once a day,
        # min(money * 10 * rate, cap).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["fund"]
        st = _fund_state(acc)
        try:
            period = cfg["time"][str(st.get("key") or "1")]
        except (KeyError, TypeError):
            period = [0, 7, 7]
        add = acc["fund_add_time"]
        start = add + datetime.timedelta(days=float(period[0]))
        end = start + datetime.timedelta(days=float(period[1]))
        over = (end + datetime.timedelta(days=float(period[2]))
                - datetime.timedelta(minutes=1))
        now = datetime.datetime.utcnow()
        last = st.get("last_time")
        if isinstance(last, datetime.datetime) and last.date() == now.date():
            return {}
        if not (end <= now < over):
            return {}
        money = float(st.get("money") or 0)
        ret = cfg.get("return") or [0, 0, 0]
        if money < float(ret[0]):
            return {}
        gain = min(int(money * 10 * float(ret[1])), int(ret[2]))
        if gain <= 0:
            return {}
        acc["coin"] = int(acc.get("coin", 0)) + gain
        st["last_time"] = now
        save_accounts(accounts)
        log("    -> fund claim +", gain, "coin=", acc["coin"])
        # PanelActivityFund.reService() reads param1.data as the new coin
        # *number* (param1 is the response envelope; server_now comes from
        # the envelope).  A dict here would break the arithmetic.
        return int(acc["coin"])

    if method == "user.get_consume_ranks":
        # 活動中心 → 消費排行 (PanelActivitySpendRank).  fixed_gift is the
        # list of already-claimed thresholds, my_coin_num drives progress,
        # and rank_list is rendered by ItemSpendRankList.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {"fixed_gift": [], "my_coin_num": 0, "rank_list": []}
        teams = _ensure_team(acc)
        aid = "A_1001_2"
        for key in teams[0]:
            if key:
                aid = str(key).split("|")[0]
                break
        # Seed once if this account predates the spend-rank tracker.
        if "spend_coin" not in acc:
            acc["spend_coin"] = 6000
            save_accounts(accounts)
        played = int(acc["spend_coin"])
        rows = [{
            "uid": uid, "zone": "1-01",
            "name": str(acc.get("nick") or uid),
            "lv": int(acc.get("lv", 25)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "avatar": {"aid": aid}, "coin_num": played,
        }]
        for i, bot in enumerate(PVP_BOTS[:8]):
            rows.append({
                "uid": bot["uid"], "zone": "1-01", "name": bot["name"],
                "lv": int(bot["lv"]),
                "vip_lv": int(3 - i // 3) if i < 8 else 0,
                "avatar": {"aid": bot["team"][0][0]},
                "coin_num": max(0, 9000 - i * 700),
            })
        rows.sort(key=lambda r: r["coin_num"], reverse=True)
        for i, row in enumerate(rows):
            row["current_rank"] = i + 1
        # re_user_get_consume_ranks() reads param1.data.fixed_gift etc.;
        # param1 is the response envelope, so return these fields directly.
        return {
            "fixed_gift": list(acc.get("spend_rank_claimed", [])),
            "my_coin_num": played,
            "rank_list": rows,
        }

    if method == "user.get_spend_fixed_gift":
        # Claim a 消費排行 milestone.  reService_award() patches gold,
        # medal, attrs.*, avatars and equips straight from this payload, so
        # return the full make_user() object.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        try:
            key = int(params.get("key"))
        except (TypeError, ValueError):
            return {}
        cfg = _cfg()["ploy_system_simple"]["spend_rank"]
        gift = (cfg.get("fixed_gift") or {}).get(str(key))
        claimed = acc.setdefault("spend_rank_claimed", [])
        if (not isinstance(gift, dict) or key in claimed
                or int(acc.get("spend_coin", 0)) < key):
            return {}
        _grant_gift(acc, gift)
        claimed.append(key)
        save_accounts(accounts)
        log("    -> spend_rank claim", key, gift)
        # PanelActivitySpendRank.reService_award() reads param1.data.gold,
        # param1.data.attrs.* etc.  param1.data is the handler return, so
        # return the user payload directly.
        return make_user(acc)

    if method == "user.welfare_reward_info":
        # 活動中心 → 福利 initial state.  info[colour] is the array of pool
        # counts shown next to each welfare_photo; number=-1 means normal
        # dust-exchange mode rather than the random jackpot animation.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["welfare"]
        st = _welfare_state(acc)
        n = int(cfg.get("number_pool", 5))
        info = [[1 + i for i in range(n)] for _ in range(4)]
        return {
            "info": info,
            "welfare_times": list(st["times"]),
            "had_reward": list(st["had_reward"]),
            "coin_times": int(st["coin_times"]),
            "number": int(st["number"]),
            "had_play": int(st["had_play"]),
        }

    if method == "user.welfare_buy_dust":
        # Buy coloured enchant dust from one welfare row.  flag -1 = free
        # single, 0 = paid single, 1 = paid ten-pack.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["welfare"]
        st = _welfare_state(acc)
        try:
            color = int(params.get("color"))
            flag = int(params.get("flag", 0))
        except (TypeError, ValueError):
            return {}
        if color < 0 or color >= 4:
            return {}
        idx = 1 if flag == 1 else 0
        try:
            price_map = cfg["dust_price"][color][idx]
        except (KeyError, IndexError, TypeError):
            return {}
        dust_color = None
        currency = None
        price = 0
        for dust_key, cur_map in price_map.items():
            for cur_key, value in cur_map.items():
                dust_color = int(dust_key)
                currency = str(cur_key)
                price = int(value)
                break
            if currency:
                break
        if currency is None:
            return {}
        free_cfg = cfg.get("free_times") or []
        is_free = (flag == -1 and color < len(free_cfg)
                   and int(free_cfg[color]) == 1
                   and int(st["times"][color]) == 0)
        if not is_free:
            if int(acc.get(currency, 0)) < price:
                return {}
            acc[currency] = int(acc.get(currency, 0)) - price
            st["coin_times"] = int(st["coin_times"]) + 1
        else:
            st["times"][color] = int(st["times"][color]) + 1
        dust = acc.get("dust_arr")
        if not isinstance(dust, list) or len(dust) < 5:
            dust = [0, 0, 0, 0, 0]
            acc["dust_arr"] = dust
        amount = 10 if flag == 1 else 1
        if dust_color is not None and 0 <= dust_color < len(dust):
            dust[dust_color] = int(dust[dust_color]) + amount
        save_accounts(accounts)
        log("    -> welfare buy dust", color, flag, currency, price,
            "-> colour", dust_color)
        return {
            "coin": int(acc.get("coin", 0)),
            "gold": int(acc.get("gold", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "dust": list(dust),
            "welfare_times": list(st["times"]),
            "coin_times": int(st["coin_times"]),
            "welfare_info": {"pos_y": int(dust_color or 0)},
        }

    if method == "user.welfare_get_reward":
        # Jackpot-mode reward claim (not normally reachable with number=-1,
        # but kept so the panel works if a number is ever set).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["welfare"]
        st = _welfare_state(acc)
        try:
            color = int(params.get("color"))
        except (TypeError, ValueError):
            return {}
        if color < 0 or color >= len(cfg.get("reward") or []):
            return {}
        if int(st["had_reward"][color]) == 1:
            return {}
        reward = cfg["reward"][color]
        _grant_gift(acc, reward)
        st["had_reward"][color] = 1
        save_accounts(accounts)
        log("    -> welfare reward", color, reward)
        user = make_user(acc)
        user.update({
            "culture_book": user["attrs"].get("culture_book", 0),
            "reward": reward,
            "had_reward": list(st["had_reward"]),
        })
        return user

    if method == "user.gamble":
        # 活動中心 → 競猜: each attempt costs return_coin[index+1][0];
        # 50% chance to return double the stake.  The callback reads
        # param1.data as the new coin balance, so return a bare number.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return 0
        cfg = _cfg()["ploy_system_simple"]["gamble"]
        coins = cfg.get("return_coin") or []
        idx = int(acc.get("gamble_index", 0))
        if idx + 1 >= len(coins):
            return int(acc.get("coin", 0))
        cost = int((coins[idx + 1] or [0])[0])
        if int(acc.get("coin", 0)) < cost:
            return int(acc.get("coin", 0))
        acc["coin"] = int(acc.get("coin", 0)) - cost
        win = random.random() < 0.5
        reward = cost * 2 if win else 0
        acc["coin"] = int(acc["coin"]) + reward
        acc["gamble_index"] = idx + 1
        save_accounts(accounts)
        log("    -> gamble", idx + 1, "cost", cost, "win" if win else "lose",
            "coin=", acc["coin"])
        return int(acc["coin"])

    if method == "user.get_gamble_reports":
        # Report ticker strings; an empty list is valid and simply leaves
        # the scroll area blank.
        return []

    if method == "user.groupon_info":
        # 活動中心 → 團購 main panel.  total_num is seeded with a small
        # fake crowd so the progress bar/milestones look alive offline.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        return _groupon_data(acc)

    if method in ("user.groupon_buy", "user.groupon_buy_one"):
        # Buy one or ten group-buy units; each unit grants one random item
        # from groupon.item.  The client reads coin/vip/new_*_soul/buy_gift
        # from the payload and reuses the rest for its progress bar.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["groupon"]
        try:
            num = 1 if method == "user.groupon_buy_one" else int(
                params.get("num", 1))
        except (TypeError, ValueError):
            num = 1
        if num not in (1, 10):
            num = 1
        price = int(cfg.get("coin", 100)) * num
        if num == 10:
            price = int(price * 0.9)
        if int(acc.get("coin", 0)) < price:
            return {}
        acc["coin"] = int(acc.get("coin", 0)) - price
        acc["groupon_my_num"] = int(acc.get("groupon_my_num", 0)) + num
        acc["groupon_total"] = int(acc.get("groupon_total", 37)) + num
        acc["groupon_consume"] = int(acc.get("groupon_consume", 0)) + price
        pool = cfg.get("item") or []
        gifts = []
        for _ in range(num):
            if not pool:
                break
            entry = random.choice(pool)
            reward = entry[0] if isinstance(entry, list) and entry else entry
            if isinstance(reward, dict):
                _grant_gift(acc, reward)
                gifts.append(reward)
        save_accounts(accounts)
        log("    -> groupon buy", num, "cost", price, "gifts", len(gifts))
        data = _groupon_data(acc)
        data.update({
            "coin": int(acc.get("coin", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "new_avatar_soul": acc.get("avatar_soul", {}),
            "new_equip_soul": acc.get("equip_soul", {}),
            "buy_gift": gifts,
        })
        return data

    if method == "user.groupon_close":
        # Event-over notification; the client stores the returned flag in
        # attrs.groupon[1].
        return 1

    if method == "user.wager_avatar":
        # 祭坛/角色抽奖 behind PanelCenterCasino A (score) and B (coin).
        # PanelCasinoA.re_wager() consumes data.new_avatars + full
        # data.attrs/records and plays the card-flip animation.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        try:
            times = int(params.get("times") or 1)
        except (TypeError, ValueError):
            times = 1
        if times not in (1, 10):
            return {}
        wager_type = str(params.get("wager_type") or "score")
        if wager_type not in ("score", "coin"):
            return {}
        try:
            free = int(params.get("free") or 0)
        except (TypeError, ValueError):
            free = 0
        # 2026-10-22: timed free-draw reset rewards are disabled.  Ignore a
        # stale client free flag and charge the normal price instead.
        free = 0
        ss = _cfg()["system_simple"]
        wa = ss["wager_avatar"]
        avatars = _ensure_avatars(acc)
        if len(avatars) + times > int(acc.get("avatar_len", 2000)):
            log("    -> wager_avatar rejected: inventory full", len(avatars))
            return {}
        now_ms = _now_ms()
        free_key = "wager_free_score" if wager_type == "score" else "wager_free_coin"
        auto_free = False
        if free:
            if times != 1:
                return {}
            cooldown = int(ss["wager_free"][0 if wager_type == "score" else 1]) \
                * 60 * 1000
            last = int(acc.get(free_key, 0) or 0)
            if last and now_ms - last < cooldown:
                log("    -> wager_avatar free draw still cooling down")
                return {}
            if wager_type == "score":
                # Only the score altar has an account-wide free-draw quota;
                # the coin altar's free draw is purely time based.
                if int(acc.get("free_wager_count", 0)) >= int(wa[15]):
                    log("    -> wager_avatar free score quota exhausted")
                    return {}
                acc["free_wager_count"] = \
                    int(acc.get("free_wager_count", 0)) + 1
            acc[free_key] = now_ms
        else:
            if wager_type == "score":
                # 2026-10-23: 金幣祭壇 now pays with gold (1000/10000),
                # not the old score/friendship currency.
                cost = int(wa[2] if times == 1 else wa[3])
                if int(acc.get("gold", 0)) < cost:
                    log("    -> wager_avatar rejected: not enough gold",
                        acc.get("gold", 0), "<", cost)
                    return {}
                acc["gold"] = int(acc.get("gold", 0)) - cost
            else:
                # 2026-10-22: the periodic "every N singles is free" reward
                # was removed with the other free draws.  Every coin draw is
                # charged at full price.
                cost = int(wa[0] if times == 1 else wa[1])
                if int(acc.get("coin", 0)) < cost:
                    log("    -> wager_avatar rejected: not enough coin",
                        acc.get("coin", 0), "<", cost)
                    return {}
                acc["coin"] = int(acc.get("coin", 0)) - cost
        # PanelCasinoA adds these medal amounts locally; mirror them.
        # The periodic auto-free single draw still counts as a paid single
        # for the medal reward, matching the client's local calculation.
        if wager_type == "coin":
            medal = int(wa[11] if free else
                        (wa[13] if times == 10 else wa[12]))
            acc["medal"] = int(acc.get("medal", 0)) + medal
        if wager_type == "score":
            # 金幣祭壇: novice-only pool with a five-star ten-pull guarantee.
            drawn = _altar_draw_gold(times)
        else:
            # 點券祭壇: all advanced heroes, cumulative 10/50 pity.
            drawn = _altar_draw_ticket(acc, times)
        new_avatars = {}
        slot = int(acc.get("next_slot", 100))
        for aid in drawn:
            key = "%s|%d" % (aid, slot)
            slot += 1
            av = _make_avatar(aid, 1)
            avatars[key] = av
            new_avatars[key] = dict(av)
        acc["next_slot"] = slot
        save_accounts(accounts)
        user = make_user(acc)
        log("    -> wager_avatar", wager_type, "x", times, "free=", free,
            "auto_free=", auto_free, "draw=", ",".join(drawn))
        return {
            "attrs": user["attrs"],
            "records": user["records"],
            "new_avatars": new_avatars,
            "score": int(acc.get("score", 0)),
            "coin": int(acc.get("coin", 0)),
            "medal": int(acc.get("medal", 0)),
            "gold": int(acc.get("gold", 0)),
            "wager_coin_1_count": int(
                acc.get("wager_coin_1_count", 0) or 0),
        }

    if method == "user.get_lottery_activity":
        # VIP 祭坛 (PanelCasinoVIP): spends 點券, returns heroes/souls, gains
        # 賭場積分 spendable in PanelInteGralExchange, and accrues VIP exp.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["extract_avatar"]
        if not _altar_activity_open(cfg):
            log("    -> get_lottery_activity rejected: activity closed")
            return {}
        try:
            flag = int(params.get("flag") or 0)
        except (TypeError, ValueError):
            flag = 0
        times = 10 if flag else 1
        cost = int(cfg.get("coin_ten" if flag else "coin_one", 0) or 0)
        avatars = _ensure_avatars(acc)
        # The 10-draw guarantee can append a 249/250 material card, so
        # reserve one extra slot.
        if len(avatars) + times + 1 > int(acc.get("avatar_len", 2000)):
            log("    -> get_lottery_activity rejected: inventory full",
                len(avatars))
            return {}
        if int(acc.get("coin", 0)) < cost:
            log("    -> get_lottery_activity rejected: not enough coin",
                acc.get("coin", 0), "<", cost)
            return {}
        acc["coin"] = int(acc.get("coin", 0)) - cost
        # payCoinVip() on the client grants VIP exp equal to the coin spent.
        acc["vip_exp"] = int(acc.get("vip_exp", 0)) + cost
        acc["vip_lv"] = _vip_level_from_exp(int(acc["vip_exp"]))
        gain = int(cfg.get("score_ten" if flag else "score_one", 0) or 0)
        acc["lottery_score"] = int(acc.get("lottery_score", 0) or 0) + gain
        drawn = _altar_draw_vip(acc, times)
        owned = _owned_aids(avatars)
        slot = int(acc.get("next_slot", 100))
        avatar_rows = []
        for aid in drawn:
            # Every drawn card becomes a real instance, including duplicate
            # heroes.  Do not convert duplicates into 英雄戰魂.
            key = "%s|%d" % (aid, slot)
            slot += 1
            av = _make_avatar(aid, 1)
            avatars[key] = av
            owned.add(aid)
            avatar_rows.append({key: dict(av)})
        acc["next_slot"] = slot
        save_accounts(accounts)
        log("    -> get_lottery_activity flag", flag, "cost", cost,
            "score", acc["lottery_score"], "draw=", ",".join(drawn))
        return {
            "coin": int(acc.get("coin", 0)),
            "score": int(acc.get("lottery_score", 0)),
            "vip_exp": int(acc.get("vip_exp", 0)),
            "vip_lv": int(acc.get("vip_lv", 0)),
            "avatars": {
                "avatar": avatar_rows,
                "avatar_soul": [],
            },
        }

    if method == "user.exchange_activity_avatar":
        # 積分兌換 (PanelInteGralExchange -> ItemInteGralExchange).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        cfg = _cfg()["ploy_system_simple"]["extract_avatar"]
        if not _altar_activity_open(cfg):
            return {}
        try:
            index = int(params.get("index"))
        except (TypeError, ValueError):
            return {}
        rows = cfg.get("exchange") or []
        if index < 0 or index >= len(rows):
            return {}
        entry = rows[index]
        if not (isinstance(entry, list) and len(entry) >= 2):
            return {}
        gift, need = entry[0], int(entry[1] or 0)
        if not isinstance(gift, dict):
            return {}
        score = int(acc.get("lottery_score", 0) or 0)
        if score < need:
            return {}
        avatars = _ensure_avatars(acc)
        slot = int(acc.get("next_slot", 100))
        cap = int(acc.get("avatar_len", 2000))
        out = {}
        for aid, count in (gift.get("avatar") or {}).items():
            try:
                count = max(0, int(count))
            except (TypeError, ValueError):
                count = 0
            if count <= 0:
                continue
            if len(avatars) + count > cap:
                return {}
            for _ in range(count):
                key = "%s|%d" % (aid, slot)
                slot += 1
                av = _make_avatar(aid, 1)
                avatars[key] = av
                out.setdefault("avatar", {})[key] = dict(av)
        for aid, count in (gift.get("avatar_soul") or {}).items():
            try:
                count = int(count)
            except (TypeError, ValueError):
                continue
            if count <= 0:
                continue
            souls = acc.setdefault("avatar_soul", {})
            souls[aid] = int(souls.get(aid, 0) or 0) + count
            out.setdefault("avatar_soul", {})[aid] = count
        acc["next_slot"] = slot
        acc["lottery_score"] = score - need
        save_accounts(accounts)
        out["score"] = int(acc["lottery_score"])
        log("    -> exchange_activity_avatar index", index, "need", need,
            "left", acc["lottery_score"])
        return out

    if method == "user.medal_exchange":
        # 勳章兌換 (PanelExchange/ItemExchange).  The client sends its local
        # medal balance, but the authoritative price is cfg.exchange.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        exch_type = str(params.get("exch_type") or "")
        exch_id = str(params.get("exch_id") or "")
        if exch_type not in ("avatar", "equip"):
            return {}
        ecfg = _cfg().get("exchange", {}).get(exch_type) or {}
        table = ecfg.get("exchange") or {}
        entry = table.get(exch_id)
        if entry is None:
            for row in ecfg.get("cycle_exchange") or []:
                if isinstance(row, dict) and exch_id in row:
                    entry = row[exch_id]
                    break
        if entry is None:
            return {}
        if exch_type == "equip":
            try:
                need = int(entry[0])
                vip_req = int(entry[1]) if len(entry) > 1 else 0
            except (TypeError, ValueError, IndexError):
                return {}
        else:
            try:
                need = int(entry)
            except (TypeError, ValueError):
                return {}
            vip_req = 0
        if int(acc.get("medal", 0)) < need:
            return {}
        if vip_req and int(acc.get("vip_lv", 0)) < vip_req:
            return {}
        if exch_type == "avatar":
            if exch_id not in AVATAR_CATALOG:
                return {}
            avatars = _ensure_avatars(acc)
            if len(avatars) >= int(acc.get("avatar_len", 2000)):
                return {}
            slot = int(acc.get("next_slot", 100))
            key = "%s|%d" % (exch_id, slot)
            acc["next_slot"] = slot + 1
            avatars[key] = _make_avatar(exch_id, 1)
            acc["medal"] = int(acc.get("medal", 0)) - need
            save_accounts(accounts)
            log("    -> medal_exchange avatar", exch_id, "cost", need,
                "left", acc["medal"])
            return {"medal": int(acc["medal"]), "avatars": avatars}
        if exch_id not in EQUIP_CATALOG:
            return {}
        eid = _final_equip_eid(exch_id)
        my, _rows = _ensure_equips(acc)
        slot = int(acc.get("next_equip", 1000))
        iid = "e%d" % slot
        acc["next_equip"] = slot + 1
        my[iid] = {
            "eid": eid, "lv": 1, "slv": 1, "sexp": 0,
            "new_4attrs": _fixed_equip_attrs(eid),
            "halo": {"lv": 0, "exp": 0},
            "symp": -1, "magic": [0, 0, 0, 0],
            "alchemy": [0, 0],
        }
        acc["medal"] = int(acc.get("medal", 0)) - need
        save_accounts(accounts)
        log("    -> medal_exchange equip", eid, "cost", need,
            "left", acc["medal"])
        return {"medal": int(acc["medal"]), "my_equips": my}

    if method in ("user.exploration_start", "user.exploration_make_army",
                  "user.exploration_refresh", "user.exploration_buy_mode",
                  "user.exploration_relive", "user.exploration_opponent",
                  "user.exploration_combat", "user.exploration_get_reward"):
        # 探險: the map walk and fight are simulated client-side (like PVE).
        # The server only seeds the RNG, supplies the two teams, and handles
        # the chest reward that advances the stage.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        st = _exploration_state(acc)
        army = st.get("army") if isinstance(st.get("army"), dict) else {}

        if method == "user.exploration_make_army":
            avatars = _ensure_avatars(acc)
            picked = {}
            ids = []
            for key in params.get("aids") or []:
                if isinstance(key, str) and key in avatars:
                    picked[key] = dict(avatars[key])
                    ids.append(key)
            st["army"] = picked
            # PanelActivityExplorationMyTeam compares cloneArray entries
            # (avatar id strings) against the dragged avatar's name; a list
            # of row arrays would make getXY() return null and crash.
            st["combat_army"] = ids
            save_accounts(accounts)
            log("    -> exploration_make_army", list(picked))
            return {"army": picked}

        if method == "user.exploration_refresh":
            st["stage"] = int(st.get("stage", 1)) + 1
            st["stage_mode"] = list(
                _EXPLORATION_MODES[st["stage"] % len(_EXPLORATION_MODES)])
            st["current_stage_finish"] = 0
            st["refresh_count"] = int(st.get("refresh_count", 5))
            save_accounts(accounts)
            return {"stage": st["stage"],
                    "stage_mode": list(st["stage_mode"]),
                    "refresh_count": st["refresh_count"],
                    "current_stage_finish": 0, "mode_buy":
                        int(st.get("mode_buy", 0)),
                    "relive_buy": 0, "vip_relive": 0,
                    "army": army}

        if method == "user.exploration_buy_mode":
            cur = st.get("stage_mode")
            try:
                mi = _EXPLORATION_MODES.index(cur)
            except ValueError:
                mi = -1
            st["stage_mode"] = list(
                _EXPLORATION_MODES[(mi + 1) % len(_EXPLORATION_MODES)])
            st["mode_buy"] = int(st.get("mode_buy", 0)) + 1
            save_accounts(accounts)
            user = make_user(acc)
            user.update({
                "stage": int(st.get("stage", 1)),
                "stage_mode": list(st["stage_mode"]),
                "refresh_count": int(st.get("refresh_count", 5)),
                "current_stage_finish":
                    int(st.get("current_stage_finish", 0)),
                "mode_buy": int(st.get("mode_buy", 0)),
                "relive_buy": 0, "vip_relive": 0,
                "army": army,
                "combat_army": st.get("combat_army") or [],
            })
            return user

        if method == "user.exploration_opponent":
            try:
                stage = int(params.get("stage") or st.get("stage", 1))
            except (TypeError, ValueError):
                stage = int(st.get("stage", 1))
            enemy = _exploration_enemy(stage)
            return {
                "name": "野區守衛 Lv.%d" % enemy["lv"],
                "power": enemy["power"],
                "is_npc": True,
                "army": enemy["rows"],
                "stage": stage,
                "stage_mode": list(st.get("stage_mode")
                                   or _EXPLORATION_MODES[0]),
            }

        if method == "user.exploration_combat":
            entries = []
            ids = []
            for key, val in army.items():
                try:
                    entries.append((str(key).split("|")[0],
                                    int(val.get("lv", 1))))
                    ids.append(str(key))
                except (AttributeError, TypeError, ValueError):
                    continue
            if not entries:
                entries = [(u["aid"], int(u.get("lv", 1)))
                           for u in _pvp_my_units(acc, 1)]
                ids = [u["aid"] for u in _pvp_my_units(acc, 1)]
            enemy = _exploration_enemy(int(st.get("stage", 1)))
            # Offline rule: a fight is always a win; the chest then becomes
            # claimable (current_stage_finish=1) exactly like the live flow.
            st["current_stage_finish"] = 1
            st["combat_army"] = ids
            save_accounts(accounts)
            log("    -> exploration_combat stage", st.get("stage"))
            return {
                "seed": 12345,
                "poke_data": {
                    "user_gift": {},
                    "gift_list": [{"gold": 200}, {"coin": 2},
                                  {"gold": 50}],
                    "poke_gift_index": 0,
                },
                "sign": 1,
                "def_th": 1,
                "client_orgin_team_a": _exploration_units(entries, 1),
                "client_orgin_team_b":
                    _exploration_units(enemy["team"], 2),
                "stage": int(st.get("stage", 1)),
                "stage_mode": list(st.get("stage_mode")
                                   or _EXPLORATION_MODES[0]),
                "refresh_count": int(st.get("refresh_count", 5)),
                "current_stage_finish": 1,
                "mode_buy": int(st.get("mode_buy", 0)),
                "relive_buy": 0, "vip_relive": 0,
                "army": army,
                "combat_army": st["combat_army"],
                "gold": int(acc.get("gold", 0)),
                "coin": int(acc.get("coin", 0)),
                "dn_stone": int(acc.get("dn_stone", 0)),
                "lv": int(acc.get("lv", 25)),
                "exp": int(acc.get("exp", 0)),
            }

        if method == "user.exploration_get_reward":
            stage = int(st.get("stage", 1))
            gift_obj = {"gold": 300 + stage * 100, "coin": 5,
                        "dn_stone": 2 * DN_STONE_REWARD_RATE}
            _grant_gift(acc, gift_obj)
            # PanelActivityExplorationMap.reback() calls
            # Tools.changeArrayToObject(gifts), which requires an Array.
            gift_list = [{"gold": gift_obj["gold"]},
                         {"coin": gift_obj["coin"]},
                         {"dn_stone": gift_obj["dn_stone"]}]
            st["stage"] = stage + 1
            st["stage_mode"] = list(
                _EXPLORATION_MODES[st["stage"] % len(_EXPLORATION_MODES)])
            st["current_stage_finish"] = 0
            save_accounts(accounts)
            user = make_user(acc)
            user.update({
                "stage": st["stage"],
                "stage_mode": list(st["stage_mode"]),
                "refresh_count": int(st.get("refresh_count", 5)),
                "current_stage_finish": 0,
                "mode_buy": int(st.get("mode_buy", 0)),
                "relive_buy": 0, "vip_relive": 0,
                "army": army,
                "combat_army": st.get("combat_army") or [],
                "gifts": gift_list,
            })
            log("    -> exploration_get_reward stage", stage, "->", st["stage"])
            return user

        return {
            "stage": int(st.get("stage", 1)),
            "stage_mode": list(st.get("stage_mode")
                               or _EXPLORATION_MODES[0]),
            "refresh_count": int(st.get("refresh_count", 5)),
            "current_stage_finish": int(st.get("current_stage_finish", 0)),
            "mode_buy": int(st.get("mode_buy", 0)),
            "relive_buy": 0, "vip_relive": 0,
            "army": army,
            "combat_army": st.get("combat_army") or [],
        }

    if method == "user.task_info":
        # PanelCenterTaskAward.reService() reads exactly these two fields.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        return {"hero_score": 0,
                "time_consumecoin": int(acc.get("time_consumecoin", 0))}

    if method == "user.task_done":
        # ItemTaskAward sends task_key/type/giftType/awardItem/task_code.
        # Response is applied as full user data; .gift is the display award.
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        task_key = params.get("task_key") or params.get("type")
        task_cfg = _cfg()["task"].get(task_key)
        if not task_cfg:
            return {}
        try:
            code = int(params.get("task_code") or 0)
        except (TypeError, ValueError):
            code = 0
        content = task_cfg.get("content") or []
        claimed = int((acc.get("task") or {}).get(task_key, 0))
        if code != claimed or code >= len(content):
            return {}
        gift = content[code].get("gift") or {}
        _grant_gift(acc, gift)
        acc.setdefault("task", {})[task_key] = claimed + 1
        save_accounts(accounts)
        log("    -> task_done", task_key, code, "gift=", gift)
        user = make_user(acc)
        user["gift"] = gift
        return user

    if method == "user.everyday_gift":
        # PanelCenterTaskAward's daily-gift rows use type "_$everyday$_N".
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        if acc is None:
            return {}
        try:
            idx = int(params.get("gnum"))
        except (TypeError, ValueError):
            typ = str(params.get("type") or "")
            try:
                idx = int(typ.rsplit("_", 1)[1])
            except (IndexError, ValueError):
                return {}
        gifts = _cfg()["everyday_gift"]
        if idx < 0 or idx >= len(gifts):
            return {}
        _ensure_daily_gift(acc)
        claimed = acc.setdefault("everyday_gift", [])
        if idx in claimed:
            return {}
        gift = gifts[idx]
        _grant_gift(acc, gift)
        claimed.append(idx)
        save_accounts(accounts)
        log("    -> everyday_gift", idx, "gift=", gift)
        user = make_user(acc)
        user["gift"] = gift
        return user

    if method == "user.get_avatar_store":
        # 英雄图鉴 (PanelHelpAvatar): avatars maps every configured id to
        # the number owned; >=0 keeps the tile visible (0 shows the mask).
        uid = request.get("uid") or params.get("uid") or "player"
        acc = accounts.get(uid)
        counts = {}
        if acc is not None:
            for key in _ensure_avatars(acc):
                aid = key.split("|")[0]
                counts[aid] = counts.get(aid, 0) + 1
        return {"avatars": {aid: max(1, counts.get(aid, 0))
                            for aid in _cfg()["avatar"]}}

    if method == "user.get":
        return {}

    return {}


# --------------------------------------------------------------------------- #
# HTTP layer
# --------------------------------------------------------------------------- #
# Help pages opened by GlobalFunction.popPanelHelp().  The client loads
# /help/<page>.html; the original server rendered these from the web CMS.
HELP_PAGES = {
    "help.html": ("遊戲幫助", [
        "《最強王者萬象版》是一款英雄收集與策略養成的放置卡牌遊戲。",
        "收集英雄、提升等級與星級，搭配隊伍挑戰副本與其他玩家。",
        "主介面下方可進入冒險、競技、公會與活動中心。",
        "遇到功能入口未解鎖時，請先提升玩家等級。",
    ]),
    # 2026-10-25 系統面板 → 關於開發者 / 開發者的信
    "developer.html": ("關於開發者", [
        "開發者：Coldfly冷蝇",
        "開發者QQ：1714019781",
        "QQ群：1132101392",
        "bilibili：搜索Coldfly冷蝇哥（https://b23.tv/bs45uMd）",
    ]),
    "letter.html": ("開發者的信", [
        "致各位夥伴的一封信",
        "各位朋友：",
        "大家好，我是 Coldfly冷蝇。",
        "歡迎來到最強王者萬象版測試服。",
        "我做這個遊戲，初衷其實很簡單：懷念早年老式回合遊戲獨有的味道。"
        "不用急促扎堆操作，慢慢思考回合佈局，琢磨技能配合，"
        "等待合適時機打出爆發，是我一直懷念的體驗。"
        "所以才一點點搭建這套玩法，設計角色與技能體系。",
        "這個項目純粹是我的個人愛好，完全免費，沒有任何充值內容。"
        "很感謝你們願意來這裡，陪我一起體驗這份屬於老回合的樂趣。"
        "遊玩時遇到 BUG、覺得機制有不合理的地方，都歡迎和我說，"
        "我會繼續慢慢調整打磨。",
        "沒有什麼宏大的期許，只希望大家放下浮躁，慢慢玩，玩得愉快。",
    ]),
    "extreme.html": ("極限挑戰", [
        "極限挑戰每天可挑戰多次，挑戰次數隨VIP等級提升。",
        "擊敗首領可獲得英雄碎片、裝備與金幣獎勵。",
        "首領戰中造成的傷害會累計到排行榜，排名越高獎勵越好。",
        "擊殺首領後全服玩家都可領取擊殺獎勵。",
    ]),
    "add_magic.html": ("裝備附魔", [
        "附魔可為裝備增加一條額外屬性。",
        "每次附魔消耗金幣，屬性種類與數值隨機產生。",
        "選擇替換後新屬性才會生效，也可保留原有屬性。",
        "裝備品質越高，可附魔出的屬性數值越高。",
    ]),
    "add_rise.html": ("裝備升級", [
        "裝備升級可提升裝備的基礎屬性與戰力。",
        "升級需要消耗金幣，可選擇升一級或一次升十級。",
        "裝備等級上限會隨召喚師等級提高：25 級時上限 50，60 級時上限 150。",
        "達到當前上限時請先提升召喚師等級；60 級後可鍛造至最高 150 級。",
        "裝備達到最高等級後無法繼續升級。",
    ]),
    "add_wash.html": ("裝備洗煉", [
        "洗煉可重新隨機裝備的附加屬性與數值。",
        "洗煉需要消耗點券，可勾選鎖定不想改變的屬性。",
        "洗煉結果可選擇保存或放棄，放棄不會扣除點券。",
        "鎖定的屬性越多，洗煉消耗的點券越多。",
    ]),
    "add_book.html": ("裝備參悟", [
        "參悟可提升裝備的技能等級與效果。",
        "參悟需要消耗其他裝備作為材料。",
        "材料裝備的品質與等級會影響參悟獲得的經驗。",
        "參悟達到上限後需要突破才能繼續提升。",
    ]),
    "zone_boss.html": ("世界首領", [
        "世界首領每日定時出現，全服玩家共同挑戰。",
        "每次攻擊消耗挑戰次數，次數每過一段時間恢復。",
        "造成的傷害會累計到傷害排行榜，排名可獲得額外獎勵。",
        "首領被擊殺後會進入下一階段，獎勵更加豐厚。",
    ]),
    "dn.html": ("德諾之陣", [
        "德諾之陣是一種特殊的陣型玩法，可為全隊提供屬性加成。",
        "升級陣法可提升陣位屬性與上陣英雄數量。",
        "不同陣位對應不同屬性，請依英雄特性安排站位。",
        "陣法重置後會返還部分升級材料。",
    ]),
    "add_welfare.html": ("福利活動", [
        "福利活動期間可消耗鑽石購買抽獎次數。",
        "每次購買可獲得隨機英雄之魂，購買次數越多機率越高。",
        "累計購買一定次數可領取額外大獎。",
        "活動結束後未使用的次數會清空，請及時使用。",
    ]),
    "hg_agreement.html": ("用戶協議", [
        "本伺服器為本地離線版，僅供個人學習與研究使用。",
        "遊戲資料保存在本機，不會上傳到任何伺服器。",
        "請勿將本程式用於商業用途。",
        "遊戲內購與儲值功能已停用，所有內容皆可透過遊戲獲得。",
    ]),
    "avatar_culture.html": ("英雄培育", [
        "培育可提升英雄的基礎屬性。",
        "培育消耗培育手冊，手冊可從副本與活動中獲得。",
        "英雄等級越高，培育可提升的屬性越多。",
        "培育等級不可超過英雄當前等級上限。",
    ]),
    "exploration.html": ("探險", [
        "派遣英雄外出探險，經過一定時間後可獲得獎勵。",
        "探險需要消耗探險次數，次數每日恢復。",
        "探險隊伍的戰力會影響可獲得的獎勵品質。",
        "使用金幣可立即完成探險。",
    ]),
    "mystery_shop.html": ("神秘商店", [
        "神秘商店每次刷新會出現不同的商品。",
        "可使用金幣或點券購買商品，部分商品需要VIP等級。",
        "商店每隔一段時間自動刷新，也可手動刷新。",
        "重新整理後商品與價格都會改變。",
    ]),
    "check_in.html": ("月簽到", [
        "每日登入遊戲即可簽到，領取當日獎勵。",
        "累計簽到天數越多，獎勵越豐厚。",
        "每月簽到進度會重置，請記得每日領取。",
        "補簽需要消耗點券。",
    ]),
    "alchemy.html": ("裝備煉化", [
        "煉化可將重複裝備轉化為煉化值。",
        "煉化值可用於提升裝備的煉化等級與屬性。",
        "消耗同名裝備可獲得額外煉化加成。",
        "煉化等級越高，消耗的材料越多。",
    ]),
    "pvp.html": ("競技場", [
        "競技場每日可挑戰其他玩家數次。",
        "勝利可提升排名並獲得競技積分。",
        "競技積分可在競技商店兌換獎勵。",
        "賽季結束後依排名發放賽季獎勵。",
    ]),
    "time_extraction.html": ("限時抽取", [
        "活動期間可消耗活動積分抽取英雄或道具。",
        "每日可免費抽取一次，免費次數在固定時間重置。",
        "十連抽可獲得額外獎勵。",
        "活動結束後未使用的活動積分會清空。",
    ]),
    "guild.html": ("公會", [
        "加入公會可與其他玩家一起挑戰公會玩法。",
        "公會等級越高，可容納的人數與解鎖的功能越多。",
        "每日可進行公會祈福、鼓舞與捐獻。",
        "退出公會後需等待一段時間才能再次加入。",
    ]),
    "guild_pvp.html": ("公會戰", [
        "公會戰每週舉行，會長或副會長可報名參賽。",
        "報名後公會成員需設定出戰隊伍。",
        "比賽採淘汰制，勝利可晉級下一輪。",
        "比賽結束後依名次發放公會與個人獎勵。",
    ]),
    "guild_shop.html": ("公會商店", [
        "公會商店可使用公會貢獻兌換道具。",
        "商品每日限購次數，VIP等級可增加購買次數。",
        "部分商品需要公會等級達到要求才能解鎖。",
        "商店每隔一段時間刷新商品。",
    ]),
    "guild_boss.html": ("公會首領", [
        "公會首領由全體成員共同挑戰。",
        "每次攻擊消耗挑戰次數，次數每日重置。",
        "擊殺首領後可獲得公會貢獻與獎勵。",
        "傷害排名越高的成員獲得的獎勵越好。",
    ]),
    "guild_research.html": ("公會研究", [
        "公會研究可提升全體成員的屬性加成。",
        "研究需要消耗公會貢獻與金幣。",
        "會長與副會長可選擇研究方向。",
        "研究等級越高，提供的加成越多。",
    ]),
    "guild_study.html": ("公會學習", [
        "公會成員可學習公會技能，獲得屬性加成。",
        "學習技能需要消耗公會貢獻。",
        "更換技能需要消耗額外貢獻。",
        "技能等級越高，提供的屬性越多。",
    ]),
    "server_pvp_helo.html": ("跨服競技", [
        "跨服競技可與其他伺服器的玩家對戰。",
        "每日可免費挑戰數次，次數隨VIP等級提升。",
        "勝利可獲得跨服積分與排名。",
        "賽季結束後依排名發放豐厚獎勵。",
    ]),
    "talent.html": ("英雄天賦", [
        "英雄達到指定星級後可開啟天賦。",
        "天賦可為英雄提供額外的屬性加成。",
        "消耗天賦點數可隨機獲得天賦。",
        "保存天賦後會覆蓋原有天賦效果。",
    ]),
}


def _help_page(title, lines):
    body = "".join("<p>%s</p>" % line for line in lines)
    return (
        "<!DOCTYPE html><html><head><meta charset='utf-8'>"
        "<style>"
        "body{margin:0;padding:16px 18px;background:#2a1a0d;color:#f4e3c1;"
        "font-family:'Microsoft JhengHei','Microsoft YaHei',sans-serif;"
        "font-size:16px;line-height:1.8}"
        "h1{margin:0 0 10px;font-size:22px;color:#ffd76e;text-align:center}"
        "p{margin:0 0 8px}"
        "</style></head><body><h1>%s</h1>%s</body></html>"
        % (title, body)
    )


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def _send(self, code, payload=b"", ctype="application/x-amf"):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        if payload:
            self.wfile.write(payload)

    def do_GET(self):
        log("GET", self.path)
        path = self.path.split("?", 1)[0]
        if path.startswith("/x/"):
            path = path[2:]
        path = path.rstrip("/")
        if path == "/notice":
            # 2026-10-25: 萬象版內測公告（使用者提供內容）。
            html = _help_page("最強王者萬象版｜內測開啟公告", [
                "歡迎來到最強王者萬象版內測！",
                "最強王者萬象版是一套底層完全重構的回合對戰測試版本，"
                "整套回合時序、結算邏輯全部重製，戰鬥內核全新改寫，"
                "兼容毒素、召喚、控制、持續傷害、技能聯動等各類戰鬥機制。"
                "取名萬象，寓意容納多樣玩法體系，探索回合對戰更多機制可能性。",
                "※ 重要提示：",
                "1. 本次為內測版本，遊戲內容完全免費。測試結束後，全部帳號、"
                "對局記錄、英雄進度等所有數據統一清除，不會繼承到後續任何版本；",
                "2. 版本尚在持續打磨階段，BUG、數值失衡、結算異常、技能改動"
                "都屬於內測階段的正常現象；",
                "3. 開發者可根據測試反饋，隨時停機維護、調整機制、關閉伺服器，"
                "不保證固定開放時長。",
                "4. 請不要使用外掛、腳本、篡改數據、惡意卡 BUG 破壞測試環境。",
                "5. 本版本原創代碼、戰鬥機制、設定內容，請不要二次打包、倒賣、"
                "私自改版後對外發布。",
                "6. 請玩家不要投入大量時間精力當作長期養成內容，"
                "所有內容隨時可能修改、刪除。",
                "歡迎各位參與測試，BUG 反饋、數值平衡建議都可以提交，"
                "助力版本持續優化！",
            ])
            self._send(200, html.encode("utf-8"), "text/html; charset=utf-8")
            return
        if path.startswith("/help/"):
            name = path[len("/help/"):]
            title, lines = HELP_PAGES.get(name, ("幫助", ["暫無此功能的說明。"]))
            html = _help_page(title, lines)
            self._send(200, html.encode("utf-8"), "text/html; charset=utf-8")
            return
        self._send(200, b"ok", "text/plain")

    def _send_json(self, code, obj):
        payload = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Allow-Methods", "POST, OPTIONS")
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(payload)
        self.close_connection = True

    def _auth_json(self, path, body):
        """POST /register and /login for web/tooling clients."""
        try:
            payload = json.loads(body.decode("utf-8") or "{}")
            if not isinstance(payload, dict):
                raise ValueError("object expected")
        except Exception:
            self._send_json(400, {"ok": False, "error": "invalid JSON body"})
            return
        account = str(payload.get("account") or payload.get("uname") or "").strip()
        password = str(payload.get("password") or "")
        err = _validate_account(account, password)
        if err:
            self._send_json(400, {"ok": False, "error": err})
            return
        if path == "/register":
            try:
                acc = create_account(account, password,
                                     str(payload.get("nickname") or account))
            except ValueError:
                self._send_json(409, {"ok": False,
                                      "error": "該帳號已存在，請換一個帳號"})
                return
            self._send_json(201, {"ok": True, "account": account,
                                  "nickname": acc.get("nick") or account,
                                  "created_at": acc.get("created_at", "")})
            return
        row = _account_row(account)
        if row is None:
            self._send_json(401, {"ok": False, "error": "帳號不存在"})
            return
        # (password verification continues below; reuse the row above)
        if not verify_account_password(account, password, row):
            self._send_json(401, {"ok": False, "error": "帳號或密碼錯誤"})
            return
        self._send_json(200, {"ok": True, "account": account,
                              "nickname": row[1], "created_at": row[2]})

    def do_OPTIONS(self):
        path = self.path.split("?", 1)[0]
        if path.startswith("/x/"):
            path = path[2:]
        path = path.rstrip("/")
        if path in ("/register", "/login"):
            self.send_response(204)
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Headers", "Content-Type")
            self.send_header("Access-Control-Allow-Methods", "POST, OPTIONS")
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        self._send(404, b"not found", "text/plain")

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(n)
        log("")
        log("=" * 70)
        log("POST", self.path, "len=", len(body),
            "ctype=", self.headers.get("Content-Type"))
        path = self.path.split("?", 1)[0]
        if path.startswith("/x/"):
            path = path[2:]
        path = path.rstrip("/")
        if path in ("/register", "/login"):
            log("  JSON auth:", path)
            try:
                self._auth_json(path, body)
            except Exception:
                log("  auth crashed:\n" + traceback.format_exc())
                self._send_json(500, {"ok": False, "error": "server error"})
            return
        ver = body[:2] if len(body) >= 2 else b"\x00\x03"
        if DEBUG_RAW_PACKETS:
            log("  RAW:", body[:400].hex())
        try:
            headers, messages = parse_packet(body)
            log("  %d AMF message(s) in this request" % len(messages))
            replies = []
            forced = os.environ.get("GAME_RESP_MODE")
            variant = forced
            for target, response_uri, decoded in messages:
                call = find_call(decoded)
                if call is None:
                    log("  !! no method in message (uri=%r); head=%s"
                        % (response_uri, body[:160].hex()))
                    result = {"method": "", "params": {}, "return_code": 0,
                              "data": {}, "server_now": datetime.datetime.utcnow()}
                else:
                    method = call["method"]
                    params = call.get("params") or {}
                    log("  CALL %s  actionID=%s  uri=%s"
                        % (method, params.get("actionID"), response_uri))
                    try:
                        data = handle(method, params, call)
                    except Exception:
                        log("  handler crashed:\n" + traceback.format_exc())
                        if method in ("user.login", "user.llogin",
                                      "user.register", "user.default_register"):
                            # Never let a crash look like a successful login.
                            key = ("register_error" if method in (
                                "user.register", "user.default_register")
                                else "login_error")
                            params[key] = "伺服器忙碌，請稍後再試"
                            data = None
                        else:
                            data = {}
                    result = {"method": method, "params": params,
                              "return_code": 0, "data": data,
                              "server_now": datetime.datetime.utcnow()}
                aid = str((result.get("params") or {}).get("actionID") or "")
                tgt, resp, own = URI_COMBOS[0][0], URI_COMBOS[0][1], None
                if aid.startswith("combo-"):
                    idx = int(aid.split("-")[1]) % len(URI_COMBOS)
                    tgt, resp = URI_COMBOS[idx]
                    log("    uri combo %d -> target=%r response=%r" % (idx, tgt, resp))
                elif aid.startswith("y-"):
                    tgt, resp = "$URI/onResult", ""
                    own = ["direct-amf3", "a1-amf3"][int(aid.split("-")[1]) % 2]
                    log("    body-test %s -> body=%s" % (aid, own))
                elif aid.startswith("x-"):
                    idx = int(aid.split("-")[1]) % len(BIG_COMBOS)
                    tgt, resp, own = BIG_COMBOS[idx]
                    log("    big combo %d -> target=%r response=%r body=%s"
                        % (idx, tgt, resp, own))
                tgt = tgt.replace("$URI", response_uri or "/1")
                resp = resp.replace("$URI", response_uri or "/1")
                replies.append((tgt, resp, own, result))
            pkt, used = build_packet(replies, ver, variant)
            log("  RESP[%s] %d bytes %s" % (used, len(pkt), pkt[:200].hex()))
            self._send(200, pkt)
        except Exception:
            log("  packet parse failed:\n" + traceback.format_exc())
            if DEBUG_RAW_PACKETS:
                log("  raw:", body[:400].hex())
            try:
                pkt, _ = build_packet(
                    [("/1", "", None,
                      {"method": "", "params": {}, "return_code": 0,
                       "data": {}, "server_now": datetime.datetime.utcnow()})],
                    ver)
            except Exception:
                log("  reply build failed:\n" + traceback.format_exc())
                pkt = b""
            self._send(200, pkt)


def _short(obj, limit=1800):
    try:
        s = json.dumps(obj, ensure_ascii=False, default=str)
    except Exception:
        s = repr(obj)
    return s if len(s) <= limit else s[:limit] + "...<truncated>"


def main():
    # Check the schema at startup.  A transient Turso outage must not stop
    # the process: every request retries and the health check stays green.
    try:
        init_db()
    except Exception:
        log("!! initial database check failed (requests will retry):\n"
            + traceback.format_exc())
    srv = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    log("game server listening on 0.0.0.0:%d" % PORT)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
