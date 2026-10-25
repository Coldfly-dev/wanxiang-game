"""Hero taxonomy and 5-star base-stat templates.

Hero numbers follow the in-game gallery order, which is the insertion order of
``hero_data.HERO_NAMES`` (1..141).  The gallery includes the A_12xx/A_13xx
skin cards and the A_1900/A_1996..A_1999 special cards, so a family number
cannot be used directly as the hero number.

Dimensions
----------
profession : attack / tank / mage / assist (from avatar_catalog ``arch``)
damageType : 1 physical, 2 magic, 3 true
tier       : novice / advanced / high, multipliers 1.00 / 1.10 / 1.25

All profession values below are the 5-star (purple card) novice baseline.
A hero's final pl is profession * tier * star, then the damage type splits
the single defence value into physical/magic defence.
"""
from hero_data import HERO_NAMES

# ---------------------------------------------------------------------------
# Gallery order.  HERO_NAMES is authored in gallery order.
# ---------------------------------------------------------------------------
HERO_ORDER = list(HERO_NAMES)
HERO_INDEX = {base: i + 1 for i, base in enumerate(HERO_ORDER)}

assert len(HERO_ORDER) == 141, "expected 141 gallery heroes, got %d" % len(HERO_ORDER)
assert HERO_ORDER[27] == "A_1028", "gallery #28 should be A_1028"
assert HERO_ORDER[31] == "A_1033", "gallery #32 should be A_1033"

# ---------------------------------------------------------------------------
# Tier classification (hero numbers)
# ---------------------------------------------------------------------------
NOVICE_HEROES = set(range(1, 22)) | set(range(127, 142))
ADVANCED_HEROES = {
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
    37, 39, 40, 41, 42,
    49, 51, 52, 53,
    57, 59, 60, 62, 67, 68, 75, 108,
}
HIGH_HEROES = set(range(1, 142)) - NOVICE_HEROES - ADVANCED_HEROES

assert NOVICE_HEROES.isdisjoint(ADVANCED_HEROES)
assert (NOVICE_HEROES | ADVANCED_HEROES | HIGH_HEROES) == set(range(1, 142))
assert len(NOVICE_HEROES) == 36
assert len(ADVANCED_HEROES) == 28
assert len(HIGH_HEROES) == 77

# ---------------------------------------------------------------------------
# Rock-paper-scissors sign type.  The client's damageRate() cycle is
# 1 -> 2 -> 3 -> 1 and grants 1.5x damage to the attacker it beats.
# ---------------------------------------------------------------------------
SIGN_TYPE_1 = {
    2, 3, 5, 8, 9, 10, 11, 12, 14, 15, 16, 17, 19, 21, 22, 23, 24, 25,
    27, 28, 29, 30, 32, 33, 35, 38, 39, 41, 43, 44, 45, 49, 50, 51, 52,
    53, 55, 60, 61, 62, 63, 65, 66, 69, 71, 72, 73, 74, 75, 76, 78, 79,
    80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 94, 95, 98, 99, 102, 103,
    104, 105, 106, 107, 109, 110, 111, 113, 114, 115, 116, 117, 118,
    121, 122, 124, 125,
}
SIGN_TYPE_2 = {
    1, 7, 13, 18, 20, 26, 31, 37, 40, 46, 47, 48, 54, 56, 57, 64, 67,
    68, 70, 77, 91, 92, 96, 97, 100, 101, 112, 120, 126,
    127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
    140, 141,
}
SIGN_TYPE_3 = {4, 6, 34, 36, 42, 58, 59, 85, 93, 108, 119, 123}

assert (SIGN_TYPE_1 | SIGN_TYPE_2 | SIGN_TYPE_3) == set(range(1, 142))
assert SIGN_TYPE_1.isdisjoint(SIGN_TYPE_2)
assert SIGN_TYPE_1.isdisjoint(SIGN_TYPE_3)
assert SIGN_TYPE_2.isdisjoint(SIGN_TYPE_3)
assert (len(SIGN_TYPE_1), len(SIGN_TYPE_2), len(SIGN_TYPE_3)) == (85, 44, 12)

# ---------------------------------------------------------------------------
# Damage type classification.  ？？？ Heroes not listed here use type 2.
# 1 = physical (subtracts physical defence), 2 = magic, 3 = true damage.
# ---------------------------------------------------------------------------
DAMAGE_TYPE_1 = {
    1, 2, 7, 8, 9, 11, 17, 21, 23, 24, 25, 26, 28, 30, 35, 39, 40, 41,
    49, 53, 57, 61, 63, 64, 68, 71, 73, 75, 77, 86, 89, 90, 95, 96, 97,
    98, 106, 107, 111, 115, 117, 118, 120, 126, 127, 128, 129, 130, 133,
    134, 136,
}
DAMAGE_TYPE_3 = {5, 12, 19, 46, 84, 91, 102, 125}
DAMAGE_TYPE_2 = set(range(1, 142)) - DAMAGE_TYPE_1 - DAMAGE_TYPE_3

assert (DAMAGE_TYPE_1 | DAMAGE_TYPE_2 | DAMAGE_TYPE_3) == set(range(1, 142))
assert DAMAGE_TYPE_1.isdisjoint(DAMAGE_TYPE_2)
assert DAMAGE_TYPE_1.isdisjoint(DAMAGE_TYPE_3)
assert DAMAGE_TYPE_2.isdisjoint(DAMAGE_TYPE_3)
assert (len(DAMAGE_TYPE_1), len(DAMAGE_TYPE_2), len(DAMAGE_TYPE_3)) == (51, 82, 8)

TIER_BY_INDEX = {}
for _i in NOVICE_HEROES:
    TIER_BY_INDEX[_i] = "novice"
for _i in ADVANCED_HEROES:
    TIER_BY_INDEX[_i] = "advanced"
for _i in HIGH_HEROES:
    TIER_BY_INDEX[_i] = "high"

SIGN_BY_INDEX = {}
for _i in SIGN_TYPE_1:
    SIGN_BY_INDEX[_i] = 1
for _i in SIGN_TYPE_2:
    SIGN_BY_INDEX[_i] = 2
for _i in SIGN_TYPE_3:
    SIGN_BY_INDEX[_i] = 3

DAMAGE_BY_INDEX = {}
for _i in DAMAGE_TYPE_1:
    DAMAGE_BY_INDEX[_i] = 1
for _i in DAMAGE_TYPE_2:
    DAMAGE_BY_INDEX[_i] = 2
for _i in DAMAGE_TYPE_3:
    DAMAGE_BY_INDEX[_i] = 3

# ---------------------------------------------------------------------------
# Range boost.  These heroes had range values that felt too short, so their
# class base range is raised to 140% of the profession template.
#
# The resulting canonical values are also used when authoring hero skills:
#   output (attack / mage) : 230 * 1.4 = 322  -> medium range
#   assist                 : 250 * 1.4 = 350  -> high range
#   tank                   : 300 * 1.4 = 420  (kept for completeness)
# ---------------------------------------------------------------------------
RANGE_BOOST_HEROES = {
    2, 3, 6, 14, 16, 21, 22, 25, 27, 29, 30, 33, 34, 36, 39, 42, 43, 44,
    45, 49, 50, 51, 52, 53, 58, 59, 60, 62, 63, 65, 66, 69, 72, 73, 74,
    76, 78, 79, 80, 81, 85, 87, 90, 93, 95, 98, 99, 102, 103, 105, 107,
    108, 109, 110, 112, 113, 114, 116, 117, 118, 119, 122, 123, 124,
    127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
    140, 141,
}
RANGE_BOOST_RATE = 1.4
RANGE_MEDIUM = 322      # 中射程: output (attack/mage) 230 * 1.4
RANGE_HIGH = 350        # 高射程: assist 250 * 1.4
RANGE_CAP = 350         # every hero's pl[9] is capped here (skills excluded)
RANGE_TANK_RAW = 420    # 坦克 300 * 1.4, before the global cap
RANGE_TANK = min(RANGE_TANK_RAW, RANGE_CAP)  # effective tank range = 350
HERO_RANGE_BONUS = 50   # 2026-10-20: every hero's final basic range +50

assert len(RANGE_BOOST_HEROES) == 79
assert RANGE_BOOST_HEROES <= set(range(1, 142))
assert RANGE_CAP >= RANGE_MEDIUM

# ---------------------------------------------------------------------------
# 5-star novice baseline per profession
# ---------------------------------------------------------------------------
PROFESSION_BASE = {
    "attack": {
        "hp": 800, "hp_lv": 60,
        "ap": 420, "ap_lv": 28,
        "def": 130, "def_lv": 4,
        "speed": 420, "range": 230,
    },
    "tank": {
        "hp": 1150, "hp_lv": 85,
        "ap": 240, "ap_lv": 17,
        "def": 175, "def_lv": 5,
        "speed": 330, "range": 300,
    },
    "mage": {
        "hp": 780, "hp_lv": 56,
        "ap": 455, "ap_lv": 30,
        "def": 125, "def_lv": 4,
        "speed": 420, "range": 230,
    },
    "assist": {
        "hp": 900, "hp_lv": 68,
        "ap": 340, "ap_lv": 24,
        "def": 140, "def_lv": 4,
        "speed": 390, "range": 250,
    },
}

TIER_FACTOR = {"novice": 1.00, "advanced": 1.10, "high": 1.25}

# Star curve, centred on 5 stars.  Speed and range are not star-scaled.
# 2026-10-25 balance pass (user request): 5★ base +15%, 6★ +20%, 7★ +25%.
# The 7★/6★ ratio stays 1.565 so 7★ remains the top tier.
STAR_FACTOR = {1: 0.55, 2: 0.65, 3: 0.75, 4: 0.88, 5: 1.15, 6: 1.38,
               7: 2.25}

# damageType -> (physical-defence multiplier, magic-defence multiplier)
DAMAGE_DEF_MULT = {
    1: (1.15, 0.85),
    2: (0.85, 1.15),
    3: (1.00, 1.00),
}


def _round(value):
    """Round half up (Python's round() is banker's rounding)."""
    return int(value + 0.5)


def _range_for(index, base_range):
    """Apply the per-hero 140% boost, then the global hero range cap.

    This only affects the hero's own pl[9].  Skill range values live in the
    skill catalog and are deliberately not capped by this function.
    """
    if index in RANGE_BOOST_HEROES:
        value = _round(base_range * RANGE_BOOST_RATE)
    else:
        value = int(base_range)
    return min(value, RANGE_CAP)


def hero_stats(base, star, arch, tier=None):
    """Return tier/sign/damage and the ten pl stats for a hero family.

    ``base`` is e.g. ``A_1028``; ``star`` is 1..6; ``arch`` is the
    avatar_catalog role.  ``tier`` may override TIER_BY_INDEX, because the
    HERO_NAMES insertion order puts the A_12xx skin cards at 104-112 while
    the real gallery (tl[9]) sorts them elsewhere.  Returns None for
    non-gallery units.
    """
    index = HERO_INDEX.get(base)
    if index is None:
        return None
    try:
        star = int(star)
    except (TypeError, ValueError):
        star = 5
    tier = tier or TIER_BY_INDEX[index]
    damage = DAMAGE_BY_INDEX[index]
    prof = PROFESSION_BASE.get(arch) or PROFESSION_BASE["attack"]
    factor = TIER_FACTOR[tier] * STAR_FACTOR.get(star, 1.0)
    pdef_mul, mdef_mul = DAMAGE_DEF_MULT[damage]
    return {
        "tier": tier,
        "sign": SIGN_BY_INDEX[index],
        "damage": damage,
        "pl": [
            _round(prof["hp"] * factor),
            _round(prof["hp_lv"] * factor),
            _round(prof["ap"] * factor),
            _round(prof["ap_lv"] * factor),
            _round(prof["def"] * factor * pdef_mul),
            _round(prof["def_lv"] * factor * pdef_mul),
            _round(prof["def"] * factor * mdef_mul),
            _round(prof["def_lv"] * factor * mdef_mul),
            int(prof["speed"]),
            _range_for(index, prof["range"]) + HERO_RANGE_BONUS,
        ],
    }
