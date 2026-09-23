"""
letsballs.com — conversational tennis club chat
Streamlit + SQLite + IG scrape + DeepSeek (strict tennis-only)
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import random
import re
import sqlite3
import threading
import time
from contextlib import contextmanager
from typing import Any, Optional
from urllib.parse import quote_plus

import requests
import streamlit as st
from bs4 import BeautifulSoup
from openai import OpenAI

try:
    from dotenv import load_dotenv

    load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"), override=True)
except ImportError:
    pass

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tennis.db")
TURSO_LOCAL_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tennis_turso.db")
AVATAR_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "avatars")
STATIC_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "static")
PROFILE_DIR = os.path.join(AVATAR_DIR, "profiles")
DEEPSEEK_BASE_URL = os.environ.get("DEEPSEEK_BASE_URL", "https://api.newcoin.top/v1").rstrip("/")
DEEPSEEK_MODEL = os.environ.get("DEEPSEEK_MODEL", "deepseek-v3.2")
# NewCoin deepseek-v3.2 is text-only. Face vision uses Face++ Detect API.
FACEPP_API_KEY = os.environ.get("FACEPP_API_KEY", "").strip()
FACEPP_API_SECRET = os.environ.get("FACEPP_API_SECRET", "").strip()
FACEPP_API_BASE = os.environ.get(
    "FACEPP_API_BASE", "https://api-us.faceplusplus.com/facepp/v3"
).rstrip("/")
MAX_TOKENS = 150
DEMO_MAX_TOKENS = 520
SCRAPE_TIMEOUT = 8
FEED_PHOTO_MAX = 3  # public: up to 3 extra feed frames after pinned
PINNED_PHOTO_MAX = 3  # profile pins first — clearest face signal
VISION_MAX_IMAGES = 4  # pinned first, then HD profile, then feed
KOL_FOLLOWER_MIN = 8_000
USE_BROWSER_IG = os.environ.get("USE_BROWSER_IG", "1").strip() not in ("0", "false", "no")

# Seeded public creator knowledge when search APIs are blocked (expand as needed).
# Last resort after web + DeepSeek prior return empty.
_KNOWN_CREATORS: dict[str, dict[str, Any]] = {
    "dinewithyy": {
        "gender": "female",
        "nationality": "Hong Kong",
        "age_guess": "late 20s–30s",
        "is_kol": True,
        "kol_niche": "foodie",
        "followers_guess": 22000,
        "display_name_guess": "Phoebe YY",
        "confidence": 0.85,
        "rationale": "Known HK foodie KOL (@dinewithyy / Phoebe YY), public dining creator.",
    },
    "cccpinky": {
        "gender": "female",
        "nationality": "Hong Kong",
        "age_guess": "unknown",
        "is_kol": False,
        "kol_niche": "none",
        "confidence": 0.7,
        "rationale": "Pinky Chan — HK-style female given name + Chan surname.",
    },
}

PIN_SALT = "letsballs-pin-v1"
ADMIN_HANDLES = {"admin", "letsballs", "letsballs_admin", "vip", "ht___here"}
DEFAULT_GAME_LOCATION = "Happy Valley"
WHATSAPP_GROUP_URL = "https://chat.whatsapp.com/LqLATzTW38oEUKIcXxXiDw?s=cl&p=i&mlu=4&ilr=4"
CHARACTER_HERO_MAX_PX = 560

_GAME_TIME_RE = re.compile(
    r"\b(?:\d{1,2}(?::\d{2})?\s*(?:a\.?m\.?|p\.?m\.?)|(?:a\.?m\.?|p\.?m\.?)|\d{1,2}:\d{2})\b",
    re.I,
)
_GAME_DATE_RE = re.compile(
    r"\b(?:mon(?:day)?|tue(?:sday)?|wed(?:nesday)?|thu(?:rsday)?|fri(?:day)?|"
    r"sat(?:urday)?|sun(?:day)?|today|tomorrow|"
    r"\d{1,2}(?:st|nd|rd|th)?\s+(?:jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*|"
    r"(?:jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s+\d{1,2}(?:st|nd|rd|th)?|"
    r"\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?)\b",
    re.I,
)

# Common Cantonese / HK / Chinese surnames (romanized) — strong locale + name-order signal
_CJK_SURNAMES = {
    "chan", "cheung", "cheng", "chow", "chiu", "chu", "chung", "fung", "ho", "hui",
    "kwan", "kwok", "lai", "lam", "lau", "law", "lee", "leung", "li", "lo", "lui",
    "ma", "mak", "man", "ng", "pang", "poon", "shui", "siu", "so", "tam", "tang",
    "tong", "tse", "tsang", "tsui", "wong", "wu", "yan", "yeung", "yip", "yiu",
    "yuen", "yung", "au", "ching", "fong", "hao", "hung", "ip", "kam", "ko",
    "kong", "ku", "kuen", "lok", "mok", "shek", "shum", "sin", "sit", "sze",
    "tai", "to", "wan", "woo", "yam", "yap", "yi", "yu", "zhang", "wang", "chen",
    "lin", "huang", "zhao", "wu", "zhou", "xu", "sun", "ma", "zhu", "hu", "guo",
    "he", "gao", "luo", "zheng", "liang", "xie", "song", "tang", "deng", "han",
    "cao", "peng", "xiao", "cai", "pan", "tian", "dong", "yuan", "cai", "feng",
}

_FEM_GIVEN = {
    "pinky", "sharon", "jenny", "kelly", "amy", "emily", "jessica", "sarah",
    "michelle", "angela", "tiffany", "chloe", "sophia", "olivia", "emma", "grace",
    "lucy", "anna", "mary", "helen", "catherine", "winnie", "cindy", "yuki",
    "hana", "mei", "ling", "yan", "joyce", "vivian", "carmen", "irene", "fiona",
    "gigi", "katie", "kate", "lisa", "linda", "susan", "sandy", "stephanie",
    "nicole", "natalie", "melissa", "rebecca", "rachel", "diana", "donna",
    "elaine", "eva", "faye", "gina", "holly", "ivy", "jackie", "joanne", "julia",
    "karen", "laura", "maggie", "monica", "nancy", "nina", "pamela", "patricia",
    "pearl", "queen", "queenie", "rita", "rose", "ruby", "sally", "selina",
    "shirley", "sonia", "stella", "sue", "tracy", "una", "valerie", "vera",
    "wendy", "yvonne", "zoe", "zoey", "bella", "aria", "mia", "luna", "cherry",
    "crystal", "angel", "annie", "betty", "carol", "doris", "ellen", "flora",
    "heidi", "jane", "jean", "joan", "kim", "lily", "may", "pam", "polly",
    "ting", "wing", "yi", "yu", "man", "ka", "chi", "sze", "siu", "pui",
    "manyee", "manee", "manyi", "man yee", "puiyi", "wingyan", "ka yan", "ka yee",
    "tsz", "tszching", "yuen", "yuenying", "sum", "summer", "autumn", "winter",
    "minty", "mint", "vian", "vianne", "vivian", "lisa", "lis", "lissa", "melissa",
    "phoebe", "phoebey", "phoebeyy", "yy", "suetyi", "sue", "suet", "yi", "shannon",
    "mina", "mimi", "mindy", "mandy", "candy", "sandy", "wendy", "cindy", "indy",
    "angel", "angela", "angeline", "kiki", "yuki", "yoyo", "coco", "koko", "bobo",
    "cherry", "peach", "honey", "baby", "bby", "queen", "queenie", "princess",
}

_MASC_GIVEN = {
    "john", "james", "david", "michael", "daniel", "chris", "jason", "kevin",
    "brian", "tony", "andy", "eric", "ryan", "jack", "tom", "peter", "wilson",
    "kenneth", "raymond", "dennis", "felix", "leo", "kai", "alex", "andrew",
    "benjamin", "bobby", "brandon", "bruce", "calvin", "charles", "derek",
    "edward", "ethan", "francis", "frank", "gary", "george", "harry", "henry",
    "ivan", "jeff", "jeffrey", "jeremy", "jimmy", "joe", "joseph", "justin",
    "keith", "ken", "larry", "lawrence", "louis", "lucas", "marcus", "mark",
    "martin", "matthew", "max", "nathan", "nick", "norman", "oscar", "patrick",
    "paul", "philip", "richard", "robert", "roger", "sam", "samuel", "scott",
    "sean", "simon", "stephen", "steve", "steven", "terry", "thomas", "tim",
    "timothy", "victor", "vincent", "wayne", "william", "winston", "woody",
    "alan", "albert", "alfred", "arthur", "bernard", "billy", "carl", "cedric",
    "chung", "ding", "hong", "kin", "ming", "pak", "shing", "tak", "wah", "wai",
    "curtis", "kurtis", "gordon", "howard", "isaac", "jordan", "kyle", "leonard",
    "marcus", "nelson", "oliver", "philip", "phillip", "phil", "quincy", "ronald", "stanley", "terry",
    "wallace", "xavier", "anthony", "benjamin", "cameron", "dominic", "edward",
}

SYSTEM_PROMPT = (
    "You are a tennis club assistant for www.playplaytennis.com. "
    "You MUST ONLY discuss tennis, game schedules, and the club. "
    "If the user asks about ANY other topic (programming, news, weather, etc.), "
    "politely refuse and pivot back to tennis. Keep answers concise. "
    "Only mention a game that is on the schedule you are given. "
    "If there is no game, say there is no game. "
    "Never promise to flag, notify, ping, watch, or message them later — "
    "this chat is not always open, so a future alert is not something you can do."
)

# Pre-generated avatar pool (40) — matched locally at signup (no image regen)
AVATAR_POOL: list[dict[str, Any]] = [
    {"file": "fat_cat.png", "emoji": "🐱", "label": "chonky cat", "tags": ["cat", "kitten", "meow", "貓", "🐈", "🐱", "🦋", "pazu", "taki", "pinky"]},
    {"file": "foodie_cat.png", "emoji": "🐱", "label": "fat foodie cat", "tags": ["cat", "foodie", "sushi", "café", "cafe", "dessert", "afternoontea", "finedine", "美食", "餓", "🐈", "🐱", "🦋", "mummy", "mom"]},
    {"file": "dumpling_cat.png", "emoji": "🐱", "label": "dumpling cat", "tags": ["dumpling", "dimsum", "bao", "cat", "foodie", "港", "🐱", "🐈", "🦋"]},
    {"file": "crosscourt_cat.png", "emoji": "🐱", "label": "tennis cat", "tags": ["cat", "tennis", "🐈", "🐱", "🦋"]},
    {"file": "tennis_pug.png", "emoji": "🐶", "label": "tennis pug", "tags": ["dog", "pug", "puppy", "狗", "🐕"]},
    {"file": "surf_dog.png", "emoji": "🐕", "label": "court shiba", "tags": ["shiba", "shiba inu", "dog", "puppy", "狗", "🐕", "vip"]},
    {"file": "surf_dog.png", "emoji": "🐶", "label": "surf dog", "tags": ["surf", "beach", "dog", "sea", "ocean", "🏄"]},
    {"file": "coffee_bear.png", "emoji": "🐻", "label": "coffee bear", "tags": ["coffee", "cafe", "咖啡", "latte", "bear"]},
    {"file": "chef_pig.png", "emoji": "🐷", "label": "chef pig", "tags": ["chef", "cook", "foodie", "kitchen", "recipe", "豬"]},
    {"file": "bakery_mouse.png", "emoji": "🐭", "label": "bakery mouse", "tags": ["bakery", "bread", "pastry", "croissant", "bake"]},
    {"file": "tea_bunny.png", "emoji": "🐰", "label": "tea bunny", "tags": ["tea", "afternoontea", "bunny", "rabbit", "🍰", "茶"]},
    {"file": "backhand_bunny.png", "emoji": "🐰", "label": "backhand bunny", "tags": ["bunny", "rabbit", "cute"]},
    {"file": "travel_camel.png", "emoji": "🐪", "label": "travel camel", "tags": ["travel", "traveller", "trip", "wander", "🌎", "🌍", "🌏", "旅"]},
    {"file": "sleepy_panda.png", "emoji": "🐼", "label": "sleepy panda", "tags": ["panda", "sleep", "nap", "chill", "lazy"]},
    {"file": "chill_koala.png", "emoji": "🐨", "label": "chill koala", "tags": ["chill", "relax", "koala", "vibe", "music"]},
    {"file": "yoga_goat.png", "emoji": "🐐", "label": "yoga goat", "tags": ["yoga", "wellness", "zen", "stretch", "mindful"]},
    {"file": "peak_goat.png", "emoji": "🐐", "label": "peak goat", "tags": ["hike", "mountain", "trail", "climb", "outdoor"]},
    {"file": "runner_horse.png", "emoji": "🐴", "label": "runner horse", "tags": ["run", "runner", "marathon", "sport", "🏃", "cycling", "🚴", "swim", "🏊"]},
    {"file": "party_parrot.png", "emoji": "🦜", "label": "party parrot", "tags": ["party", "fun", "nightlife", "dance", "cocktail", "🍸"]},
    {"file": "bookworm_owl.png", "emoji": "🦉", "label": "bookworm owl", "tags": ["book", "read", "study", "learn", "writer"]},
    {"file": "gamer_hamster.png", "emoji": "🐹", "label": "gamer hamster", "tags": ["gamer", "game", "esport", "stream", "twitch"]},
    {"file": "beach_crab.png", "emoji": "🦀", "label": "beach crab", "tags": ["beach", "sea", "island", "vacation", "sand"]},
    {"file": "night_raccoon.png", "emoji": "🦝", "label": "night raccoon", "tags": ["night", "owl", "late", "nightlife", "raccoon"]},
    {"file": "rally_raccoon.png", "emoji": "🦝", "label": "rally raccoon", "tags": ["raccoon", "mischief"]},
    {"file": "ace_axolotl.png", "emoji": "🦎", "label": "ace axolotl", "tags": ["axolotl", "unique", "pink"]},
    {"file": "lob_llama.png", "emoji": "🦙", "label": "lob llama", "tags": ["llama", "drama"]},
    {"file": "volley_fox.png", "emoji": "🦊", "label": "volley fox", "tags": ["fox", "sly", "clever"]},
    {"file": "smash_sloth.png", "emoji": "🦥", "label": "smash sloth", "tags": ["sloth", "slow", "weekend"]},
    {"file": "dropshot_duck.png", "emoji": "🦆", "label": "dropshot duck", "tags": ["duck", "quack"]},
    {"file": "topspin_turtle.png", "emoji": "🐢", "label": "topspin turtle", "tags": ["turtle", "steady"]},
    {"file": "slice_seal.png", "emoji": "🦭", "label": "slice seal", "tags": ["seal", "swim", "dive", "🤿"]},
    {"file": "baseline_beaver.png", "emoji": "🦫", "label": "baseline beaver", "tags": ["beaver", "builder", "work"]},
    {"file": "net_nudibranch.png", "emoji": "🐚", "label": "net nudibranch", "tags": ["ocean", "reef", "color"]},
    {"file": "serve_sparrow.png", "emoji": "🐦", "label": "serve sparrow", "tags": ["bird", "sparrow", "fly"]},
    {"file": "deuce_dolphin.png", "emoji": "🐬", "label": "deuce dolphin", "tags": ["dolphin", "ocean", "swim"]},
    {"file": "advantage_alpaca.png", "emoji": "🦙", "label": "advantage alpaca", "tags": ["alpaca", "fluffy"]},
    {"file": "overhead_otter.png", "emoji": "🦦", "label": "overhead otter", "tags": ["otter", "playful", "river"]},
    {"file": "forehand_frog.png", "emoji": "🐸", "label": "forehand frog", "tags": ["frog", "green", "jump"]},
    {"file": "matchpoint_meerkat.png", "emoji": "🐿️", "label": "matchpoint meerkat", "tags": ["meerkat", "watch", "alert"]},
    {"file": "spinny_squirrel.png", "emoji": "🐿️", "label": "spinny squirrel", "tags": ["squirrel", "energy", "nut"]},
    {"file": "court_capybara.png", "emoji": "🐹", "label": "court capybara", "tags": ["capybara", "chill", "zen", "friend"]},
]

# Merge extra pre-generated animals from disk, then keep only files that still exist
_EXTRA_POOL_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "avatar_pool_extra.json")
try:
    with open(_EXTRA_POOL_PATH, encoding="utf-8") as _f:
        _extra = json.load(_f)
    if isinstance(_extra, list):
        _existing = {p["file"] for p in AVATAR_POOL}
        for _row in _extra:
            if isinstance(_row, dict) and _row.get("file") and _row["file"] not in _existing:
                AVATAR_POOL.append(_row)
                _existing.add(_row["file"])
except Exception:
    pass

# Refresh pool against avatars/ (user may delete characters anytime)
AVATAR_POOL[:] = [
    p for p in AVATAR_POOL
    if isinstance(p, dict)
    and p.get("file")
    and os.path.isfile(os.path.join(AVATAR_DIR, p["file"]))
]

# Assignment / welcome portraits fill the chat column; banner stays compact
BANNER_IMAGE_WIDTH = 160

# Legacy emoji map for admin seed / older names
TENNIS_ANIMALS: dict[str, str] = {
    "Rally Raccoon": "🦝",
    "Ace Axolotl": "🦎",
    "Lob Llama": "🦙",
    "Volley Fox": "🦊",
    "Smash Sloth": "🦥",
    "Dropshot Duck": "🦆",
    "Topspin Turtle": "🐢",
    "Slice Seal": "🦭",
    "Baseline Beaver": "🦫",
    "Net Nudibranch": "🐚",
    "Serve Sparrow": "🐦",
    "Deuce Dolphin": "🐬",
    "Advantage Alpaca": "🦙",
    "Crosscourt Cat": "🐱",
    "Overhead Otter": "🦦",
    "Backhand Bunny": "🐰",
    "Forehand Frog": "🐸",
    "Matchpoint Meerkat": "🐿️",
    "Court Shiba": "🐕",
    "Spinny Squirrel": "🐿️",
    "Court Capybara": "🐹",
}

ANIMAL_PHOTO_FILES: dict[str, str] = {
    **{p["label"]: p["file"] for p in AVATAR_POOL},
    **{name: f"{name.lower().replace(' ', '_')}.png" for name in TENNIS_ANIMALS},
}
# Fix known filename mismatches
ANIMAL_PHOTO_FILES.update({
    "Rally Raccoon": "rally_raccoon.png",
    "Ace Axolotl": "ace_axolotl.png",
    "Crosscourt Cat": "crosscourt_cat.png",
    "Matchpoint Meerkat": "matchpoint_meerkat.png",
    "Court Shiba": "surf_dog.png",
    "Court Capybara": "court_capybara.png",
})

ANIMAL_NAMES = list(TENNIS_ANIMALS.keys())
CLUB_AVATAR = os.path.join(AVATAR_DIR, "club_tennis.png")
CLUB_TENNIS_FILE = "club_tennis.png"
CLUB_TENNIS_LABEL = "club tennis"
CLUB_TENNIS_EMOJI = "🎾"

# AI club chat: women clearly under 40 (nationality is not a gate)
_ALLOWED_NAT_KEYS = (
    "hong kong", "hk", "hkg", "taiwan", "taiwanese", "china", "chinese",
    "chinese-speaking", "japan", "japanese", "korea", "korean", "south korea",
)
FOODIE_CAT_AVATAR = os.path.join(AVATAR_DIR, "foodie_cat.png")

# Emoji → strong avatar boosts (checked in bio / scraped text as-is)
# Butterfly maps to cat per club taste: pretty + playful → cat portraits
EMOJI_AVATAR_RULES: list[dict[str, Any]] = [
    {
        "emojis": ["🐱", "🐈", "😺", "😸", "😻", "😽", "😹", "🙀", "😿", "😾", "🐈‍⬛"],
        "files": ["fat_cat.png", "foodie_cat.png", "dumpling_cat.png", "crosscourt_cat.png"],
        "boost": 14,
        "reason": "cat emoji in bio",
    },
    {
        "emojis": ["🦋"],
        "files": ["fat_cat.png", "foodie_cat.png", "crosscourt_cat.png", "dumpling_cat.png"],
        "boost": 12,
        "reason": "butterfly emoji → pretty cat energy",
    },
    {
        "emojis": ["🐶", "🐕", "🐩", "🦮", "🐕‍🦺"],
        "files": ["tennis_pug.png", "surf_dog.png"],
        "boost": 14,
        "reason": "dog emoji in bio",
    },
    {
        "emojis": ["🌎", "🌍", "🌏", "✈️", "🧳", "🗺️"],
        "files": ["travel_camel.png"],
        "boost": 12,
        "reason": "travel emoji in bio",
    },
    {
        "emojis": ["🏄", "🏄‍♀️", "🏄‍♂️", "🏖️", "🌊"],
        "files": ["surf_dog.png", "beach_crab.png", "slice_seal.png"],
        "boost": 10,
        "reason": "beach/surf emoji in bio",
    },
    {
        "emojis": ["🏃", "🏃‍♀️", "🏃‍♂️", "🚴", "🚴‍♀️", "🏊", "🏊‍♀️"],
        "files": ["runner_horse.png"],
        "boost": 10,
        "reason": "sport emoji in bio",
    },
    {
        "emojis": ["🍣", "🍰", "☕", "🍸", "🍜"],
        "files": ["foodie_cat.png", "chef_pig.png", "coffee_bear.png", "tea_bunny.png"],
        "boost": 8,
        "reason": "food/drink emoji in bio",
    },
    {
        "emojis": ["🐼"],
        "files": ["sleepy_panda.png"],
        "boost": 12,
        "reason": "panda emoji in bio",
    },
    {
        "emojis": ["🐨"],
        "files": ["chill_koala.png"],
        "boost": 12,
        "reason": "koala emoji in bio",
    },
    {
        "emojis": ["🦊"],
        "files": ["volley_fox.png"],
        "boost": 12,
        "reason": "fox emoji in bio",
    },
    {
        "emojis": ["🐰", "🐇"],
        "files": ["tea_bunny.png", "backhand_bunny.png"],
        "boost": 12,
        "reason": "bunny emoji in bio",
    },
]

# Auth flow states
NEED_IG = "need_ig"
NEED_PIN_SIGNUP = "need_pin_signup"
NEED_PIN_LOGIN = "need_pin_login"
LOGGED_IN = "logged_in"


def animal_photo_path(animal: Optional[str], avatar_path: Optional[str] = None) -> str:
    """Portrait path: custom avatar → species photo → any available pool file → club ball."""
    candidates: list[str] = []
    if avatar_path:
        candidates.append(
            avatar_path if os.path.isabs(avatar_path) else os.path.join(AVATAR_DIR, str(avatar_path))
        )
    fname = ANIMAL_PHOTO_FILES.get(animal or "")
    if fname:
        candidates.append(os.path.join(AVATAR_DIR, fname))
    # label may already be a pool label
    for p in AVATAR_POOL:
        if p.get("label") == animal or p.get("file") == animal:
            candidates.append(os.path.join(AVATAR_DIR, p["file"]))
    for path in candidates:
        if path and os.path.isfile(path):
            return path
    # last resort: first remaining pool portrait
    for p in AVATAR_POOL:
        path = os.path.join(AVATAR_DIR, p["file"])
        if os.path.isfile(path):
            return path
    if os.path.isfile(CLUB_AVATAR):
        return CLUB_AVATAR
    return TENNIS_ANIMALS.get(animal or "", "🎾")


def club_avatar() -> str:
    return CLUB_AVATAR if os.path.isfile(CLUB_AVATAR) else "🎾"


def completion_text(completion: Any) -> str:
    """NewCoin may return a bare string; official OpenAI shape uses .choices."""
    if completion is None:
        return ""
    if isinstance(completion, str):
        return completion.strip()
    try:
        return (completion.choices[0].message.content or "").strip()
    except Exception:
        return str(completion).strip()


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Database — local SQLite, or Turso (durable on Streamlit Cloud)
# ---------------------------------------------------------------------------


def _secret_or_env(name: str) -> str:
    val = (os.environ.get(name) or "").strip()
    if val:
        return val
    try:
        return str(st.secrets.get(name, "") or "").strip()
    except Exception:
        return ""


def turso_creds() -> tuple[str, str]:
    return _secret_or_env("TURSO_DATABASE_URL"), _secret_or_env("TURSO_AUTH_TOKEN")


def using_durable_db() -> bool:
    url, token = turso_creds()
    return bool(url and token)


def _is_streamlit_cloud() -> bool:
    return bool(
        os.environ.get("STREAMLIT_SHARING_MODE")
        or os.environ.get("STREAMLIT_CLOUD")
        or os.path.isdir("/mount/src")
    )


def persistence_warning_for_admin() -> str:
    """Streamlit Cloud wipes local SQLite on reboot unless Turso is configured."""
    if using_durable_db():
        return ""
    if not _is_streamlit_cloud():
        return ""
    return (
        "\n\n⚠️ **Storage warning:** this Cloud host resets local files on reboot. "
        "Deleted games/users can reappear from an old snapshot, or vanish. "
        "Add free **Turso** secrets (`TURSO_DATABASE_URL`, `TURSO_AUTH_TOKEN`) "
        "so the club board stays permanent."
    )


def _dict_row_factory(cursor, row):
    if cursor.description is None:
        return row
    return {col[0]: row[i] for i, col in enumerate(cursor.description)}


def _open_db_connection():
    """
    Prefer Turso when secrets exist (survives Streamlit Cloud reboots).
    Otherwise use local tennis.db (fine on your PC; ephemeral on Cloud).
    """
    url, token = turso_creds()
    if url and token:
        try:
            import libsql

            # Embedded replica: SQLite-compatible API + cloud primary
            conn = libsql.connect(
                TURSO_LOCAL_PATH,
                sync_url=url,
                auth_token=token,
            )
            try:
                conn.sync()
            except Exception:
                pass
            if hasattr(conn, "row_factory"):
                conn.row_factory = _dict_row_factory
            return conn, True
        except Exception:
            try:
                import libsql

                conn = libsql.connect(database=url, auth_token=token)
                if hasattr(conn, "row_factory"):
                    conn.row_factory = _dict_row_factory
                return conn, True
            except Exception:
                pass
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn, False


def _run_script(conn, script: str) -> None:
    if hasattr(conn, "executescript"):
        conn.executescript(script)
        return
    for chunk in script.split(";"):
        stmt = chunk.strip()
        if stmt:
            conn.execute(stmt)


@contextmanager
def get_conn():
    conn, durable = _open_db_connection()
    try:
        yield conn
        conn.commit()
        if durable and hasattr(conn, "sync"):
            try:
                conn.sync()
            except Exception:
                pass
    except Exception:
        try:
            conn.rollback()
        except Exception:
            pass
        raise
    finally:
        try:
            conn.close()
        except Exception:
            pass


def _as_dict(row) -> dict:
    if row is None:
        return {}
    if isinstance(row, dict):
        return dict(row)
    try:
        return dict(row)
    except Exception:
        return {}


def _pragma_signup_cols(conn) -> set[str]:
    names = set()
    for r in conn.execute("PRAGMA table_info(game_signups)").fetchall():
        if isinstance(r, dict):
            names.add(r.get("name") or "")
        else:
            names.add(r[1])
    return {n for n in names if n}


def format_handle(ig_handle: str) -> str:
    """Always display handles with a leading @."""
    h = normalize_handle(ig_handle)
    return f"@{h}" if h else ""


def init_db() -> None:
    os.makedirs(PROFILE_DIR, exist_ok=True)
    with get_conn() as conn:
        _run_script(
            conn,
            """
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ig_handle TEXT UNIQUE NOT NULL,
                pin_hash TEXT,
                animal TEXT,
                vibe TEXT,
                animal_emoji TEXT,
                mascot TEXT,
                avatar_path TEXT,
                ig_photo_path TEXT,
                gender TEXT,
                nationality TEXT,
                age_guess TEXT,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP
            );

            CREATE TABLE IF NOT EXISTS games (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                when_text TEXT NOT NULL,
                location TEXT,
                spots INTEGER NOT NULL DEFAULT 4,
                notes TEXT,
                created_by TEXT,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP
            );

            CREATE TABLE IF NOT EXISTS game_signups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                game_id INTEGER NOT NULL,
                ig_handle TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                admin_seen INTEGER NOT NULL DEFAULT 0,
                UNIQUE(game_id, ig_handle)
            );
            """,
        )
        # Light migrations for older DBs
        def _col_names(pragma_rows):
            names = set()
            for r in pragma_rows:
                if isinstance(r, dict):
                    names.add(r.get("name") or r.get("Name"))
                else:
                    names.add(r[1])
            return {n for n in names if n}

        cols = _col_names(conn.execute("PRAGMA table_info(users)").fetchall())
        if "mascot" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN mascot TEXT")
        if "avatar_path" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN avatar_path TEXT")
        if "ig_photo_path" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN ig_photo_path TEXT")
        if "gender" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN gender TEXT")
        if "nationality" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN nationality TEXT")
        if "age_guess" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN age_guess TEXT")
        if "ai_enabled" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN ai_enabled INTEGER DEFAULT 1")
        if "gate_override" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN gate_override INTEGER")
        if "gate_detail" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN gate_detail TEXT")
        if "assign_why" not in cols:
            conn.execute("ALTER TABLE users ADD COLUMN assign_why TEXT")
        signup_cols = _col_names(conn.execute("PRAGMA table_info(game_signups)").fetchall())
        if signup_cols and "admin_seen" not in signup_cols:
            conn.execute(
                "ALTER TABLE game_signups ADD COLUMN admin_seen INTEGER NOT NULL DEFAULT 0"
            )
    seed_admin_user()


def seed_admin_user() -> None:
    """Ensure @vip exists as admin with the club PIN. Renames the old vipstarbucks row."""
    handle = "vip"
    pin = "0413"
    animal = "Court Shiba"
    vibe = "Club captain energy — books the courts, then aces the banter."
    emoji = TENNIS_ANIMALS.get(animal) or "🐕"
    avatar_path = "surf_dog.png"
    with get_conn() as conn:
        old = conn.execute(
            "SELECT id FROM users WHERE lower(ig_handle) = ?",
            ("vipstarbucks",),
        ).fetchone()
        row = conn.execute(
            "SELECT id FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
        if old and not row:
            conn.execute(
                "UPDATE users SET ig_handle = ? WHERE id = ?",
                (handle, old["id"]),
            )
            row = old
        if row:
            conn.execute(
                """
                UPDATE users
                SET pin_hash = ?, animal = ?, vibe = ?, animal_emoji = ?,
                    mascot = ?, avatar_path = ?, ai_enabled = 1
                WHERE id = ?
                """,
                (hash_pin(pin), animal, vibe, emoji, animal, avatar_path, row["id"]),
            )
        else:
            conn.execute(
                """
                INSERT INTO users (
                    ig_handle, pin_hash, animal, vibe, animal_emoji, mascot, avatar_path, ai_enabled
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, 1)
                """,
                (handle, hash_pin(pin), animal, vibe, emoji, animal, avatar_path),
            )


def hash_pin(pin: str) -> str:
    return hashlib.sha256(f"{PIN_SALT}:{pin}".encode("utf-8")).hexdigest()


def normalize_handle(raw: str) -> str:
    handle = (raw or "").strip().lstrip("@").split("/")[-1].split("?")[0].strip()
    return handle.lower()


def get_user_by_handle(ig_handle: str) -> Optional[dict]:
    handle = normalize_handle(ig_handle)
    with get_conn() as conn:
        row = conn.execute(
            "SELECT * FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
    return _as_dict(row) if row else None


def ensure_pending_handle(ig_handle: str) -> None:
    """Persist the IG handle as soon as it is entered (before PIN / scrape finish)."""
    handle = normalize_handle(ig_handle)
    if not handle:
        return
    with get_conn() as conn:
        existing = conn.execute(
            "SELECT id FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
        if existing:
            return
        conn.execute(
            "INSERT INTO users (ig_handle, pin_hash) VALUES (?, NULL)",
            (handle,),
        )


def drop_unfinished_handle(ig_handle: str) -> None:
    """Remove a signup that never got a PIN. A missing Instagram page must not stay gated in."""
    handle = normalize_handle(ig_handle)
    if not handle:
        return
    with get_conn() as conn:
        conn.execute(
            "DELETE FROM users WHERE lower(ig_handle) = ? AND pin_hash IS NULL",
            (handle,),
        )


def _tell_profile_missing(at: str) -> None:
    append_assistant(
        f"**{at}** doesn’t exist on Instagram. "
        "That page says the link is broken, or the account was removed."
    )


def _profile_card_seen(scrape: dict) -> bool:
    """True only when a real public card was read — not a guess from the handle spelling."""
    for field in scrape.get("fields") or []:
        if field.startswith(("full_name:", "biography:", "followers:")) and field.split(":", 1)[-1].strip():
            return True
    return bool(scrape.get("ig_photo_path"))


def _tell_profile_unreadable(at: str) -> None:
    append_assistant(
        f"I couldn’t open **{at}** on Instagram just now, so that account was not signed in. "
        "Try the handle again in a bit."
    )


def upsert_pending_user(
    ig_handle: str,
    animal: str,
    vibe: str,
    emoji: str,
    mascot: str = "",
    avatar_path: str = "",
    ig_photo_path: str = "",
    gender: str = "",
    nationality: str = "",
    age_guess: str = "",
    ai_enabled: int = 1,
    gate_detail: str = "",
    assign_why: str = "",
) -> None:
    """Save identity before PIN is set (pin_hash stays NULL until signup finishes)."""
    handle = normalize_handle(ig_handle)
    mascot = mascot or animal
    with get_conn() as conn:
        existing = conn.execute(
            "SELECT id, pin_hash, ig_photo_path FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
        if existing and existing["pin_hash"]:
            return  # fully registered — don't overwrite
        photo = ig_photo_path or (existing["ig_photo_path"] if existing else None)
        if existing:
            conn.execute(
                """
                UPDATE users
                SET animal = ?, vibe = ?, animal_emoji = ?, mascot = ?,
                    avatar_path = ?, ig_photo_path = ?,
                    gender = ?, nationality = ?, age_guess = ?, ai_enabled = ?,
                    gate_detail = ?, assign_why = ?
                WHERE id = ?
                """,
                (
                    animal,
                    vibe,
                    emoji,
                    mascot,
                    avatar_path or None,
                    photo or None,
                    gender or None,
                    nationality or None,
                    age_guess or None,
                    1 if ai_enabled else 0,
                    gate_detail or None,
                    assign_why or None,
                    existing["id"],
                ),
            )
        else:
            conn.execute(
                """
                INSERT INTO users (
                    ig_handle, pin_hash, animal, vibe, animal_emoji, mascot,
                    avatar_path, ig_photo_path, gender, nationality, age_guess,
                    ai_enabled, gate_detail, assign_why
                )
                VALUES (?, NULL, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    handle,
                    animal,
                    vibe,
                    emoji,
                    mascot,
                    avatar_path or None,
                    photo or None,
                    gender or None,
                    nationality or None,
                    age_guess or None,
                    1 if ai_enabled else 0,
                    gate_detail or None,
                    assign_why or None,
                ),
            )


def finalize_signup(ig_handle: str, pin: str) -> Optional[dict]:
    handle = normalize_handle(ig_handle)
    with get_conn() as conn:
        conn.execute(
            "UPDATE users SET pin_hash = ? WHERE lower(ig_handle) = ?",
            (hash_pin(pin), handle),
        )
        row = conn.execute(
            "SELECT * FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
    return _as_dict(row) if row else None


def verify_pin(ig_handle: str, pin: str) -> Optional[dict]:
    user = get_user_by_handle(ig_handle)
    if not user or not user.get("pin_hash"):
        return None
    if user["pin_hash"] != hash_pin(pin):
        return None
    return user


def list_games(limit: int = 40) -> list[dict]:
    with get_conn() as conn:
        rows = conn.execute(
            """
            SELECT id, when_text, location, spots, notes, created_by, created_at
            FROM games ORDER BY id DESC LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [_as_dict(r) for r in rows]


def insert_game(
    when_text: str,
    spots: int = 4,
    location: str = "",
    notes: str = "",
    created_by: str = "admin",
) -> int:
    with get_conn() as conn:
        cur = conn.execute(
            """
            INSERT INTO games (when_text, location, spots, notes, created_by)
            VALUES (?, ?, ?, ?, ?)
            """,
            (when_text.strip(), (location or "").strip(), max(1, int(spots)), notes.strip(), created_by),
        )
        return int(cur.lastrowid)


def delete_game(game_id: int) -> tuple[bool, dict]:
    """Delete a game and its signups. Returns (ok, game_snapshot)."""
    with get_conn() as conn:
        row = conn.execute(
            "SELECT id, when_text, location, spots FROM games WHERE id = ?",
            (int(game_id),),
        ).fetchone()
        if not row:
            return False, {}
        conn.execute("DELETE FROM game_signups WHERE game_id = ?", (int(game_id),))
        conn.execute("DELETE FROM games WHERE id = ?", (int(game_id),))
    return True, _as_dict(row)


def admin_add_user(ig_handle: str, pin: str) -> tuple[str, dict]:
    """
    Create or update a member with a PIN, gated in.
    Returns ('created'|'updated'|'bad', user).
    """
    handle = normalize_handle(ig_handle)
    if not handle or not re.match(r"^[A-Za-z0-9._]{2,30}$", handle):
        return "bad", {}
    if not re.fullmatch(r"\d{4}", pin or ""):
        return "bad", {}
    existing = get_user_by_handle(handle)
    animal = "club tennis"
    emoji = CLUB_TENNIS_EMOJI
    vibe = "Added by admin."
    avatar_path = CLUB_TENNIS_FILE
    with get_conn() as conn:
        if existing:
            conn.execute(
                """
                UPDATE users
                SET pin_hash = ?, ai_enabled = 1, gate_override = 1,
                    animal = COALESCE(NULLIF(animal, ''), ?),
                    mascot = COALESCE(NULLIF(mascot, ''), ?),
                    animal_emoji = COALESCE(NULLIF(animal_emoji, ''), ?),
                    avatar_path = COALESCE(NULLIF(avatar_path, ''), ?),
                    vibe = COALESCE(NULLIF(vibe, ''), ?)
                WHERE lower(ig_handle) = ?
                """,
                (
                    hash_pin(pin),
                    animal,
                    animal,
                    emoji,
                    avatar_path,
                    vibe,
                    handle,
                ),
            )
            return "updated", get_user_by_handle(handle) or {}
        conn.execute(
            """
            INSERT INTO users (
                ig_handle, pin_hash, animal, vibe, animal_emoji, mascot,
                avatar_path, ai_enabled, gate_override, gate_detail, assign_why
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, 1, 1, ?, ?)
            """,
            (
                handle,
                hash_pin(pin),
                animal,
                vibe,
                emoji,
                animal,
                avatar_path,
                "Admin created this account and forced gate in.",
                "Admin created account.",
            ),
        )
    return "created", get_user_by_handle(handle) or {}


def admin_delete_user(ig_handle: str) -> tuple[str, dict]:
    """
    Delete a member and their game signups (spots restored).
    Returns ('deleted'|'missing'|'protected', user_or_empty).
    """
    handle = normalize_handle(ig_handle)
    if not handle:
        return "missing", {}
    if handle in ADMIN_HANDLES:
        return "protected", {"ig_handle": handle}
    user = get_user_by_handle(handle)
    if not user:
        return "missing", {}
    with get_conn() as conn:
        rows = conn.execute(
            "SELECT game_id FROM game_signups WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchall()
        for r in rows:
            conn.execute(
                "UPDATE games SET spots = spots + 1 WHERE id = ?",
                (r["game_id"],),
            )
        conn.execute(
            "DELETE FROM game_signups WHERE lower(ig_handle) = ?",
            (handle,),
        )
        conn.execute(
            "DELETE FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        )
    return "deleted", user


def pending_admin_signup_notices() -> list[dict]:
    with get_conn() as conn:
        cols = _pragma_signup_cols(conn)
        if "admin_seen" not in cols:
            return []
        rows = conn.execute(
            """
            SELECT s.id AS signup_id, s.ig_handle, s.created_at,
                   g.id AS game_id, g.when_text, g.location, g.spots
            FROM game_signups s
            JOIN games g ON g.id = s.game_id
            WHERE COALESCE(s.admin_seen, 0) = 0
            ORDER BY s.id ASC
            """
        ).fetchall()
    return [_as_dict(r) for r in rows]


def mark_admin_signups_seen(signup_ids: list[int]) -> None:
    if not signup_ids:
        return
    with get_conn() as conn:
        cols = _pragma_signup_cols(conn)
        if "admin_seen" not in cols:
            return
        conn.executemany(
            "UPDATE game_signups SET admin_seen = 1 WHERE id = ?",
            [(int(i),) for i in signup_ids],
        )


def format_admin_signup_notices(rows: list[dict]) -> str:
    if not rows:
        return ""
    lines = ["**New game signups since last check**"]
    for r in rows:
        when = r.get("when_text") or "a game"
        loc = r.get("location") or DEFAULT_GAME_LOCATION
        lines.append(
            f"- @{r.get('ig_handle')} joined **#{r.get('game_id')}** {when} @ {loc} "
            f"({r.get('spots')} spots left)"
        )
    return "\n".join(lines)


def consume_admin_signup_notices() -> str:
    """Return unread signup notices for admins and mark them seen."""
    rows = pending_admin_signup_notices()
    if not rows:
        return ""
    mark_admin_signups_seen([int(r["signup_id"]) for r in rows])
    return format_admin_signup_notices(rows)


def games_as_context() -> str:
    games = list_games()
    if not games:
        return "No games are currently scheduled."
    lines = []
    for g in games:
        loc = g.get("location") or DEFAULT_GAME_LOCATION
        notes = f" ({g['notes']})" if g.get("notes") else ""
        lines.append(f"- #{g['id']}: {g['when_text']} @ {loc} — {g['spots']} spots{notes}")
    return "Scheduled games (live from database):\n" + "\n".join(lines)


def list_game_signups() -> list[dict]:
    """Games with the Instagram handles that held a spot, newest game first."""
    with get_conn() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS game_signups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                game_id INTEGER NOT NULL,
                ig_handle TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(game_id, ig_handle)
            )
            """
        )
        games = conn.execute(
            """
            SELECT id, when_text, location, spots, notes
            FROM games
            ORDER BY id DESC
            """
        ).fetchall()
        out: list[dict] = []
        for g in games:
            rows = conn.execute(
                """
                SELECT ig_handle, created_at
                FROM game_signups
                WHERE game_id = ?
                ORDER BY id ASC
                """,
                (g["id"],),
            ).fetchall()
            out.append(
                {
                    **_as_dict(g),
                    "signups": [_as_dict(r) for r in rows],
                }
            )
    return out


def signups_as_context() -> str:
    games = list_game_signups()
    if not games:
        return "No games are currently scheduled."
    blocks: list[str] = []
    for g in games:
        loc = g.get("location") or DEFAULT_GAME_LOCATION
        people = g.get("signups") or []
        header = (
            f"**#{g['id']}** {g['when_text']} @ {loc} — "
            f"{len(people)} registered · {g['spots']} spots left"
        )
        if not people:
            blocks.append(f"{header}\n- (nobody yet)")
            continue
        names = "\n".join(f"- @{s['ig_handle']}" for s in people)
        blocks.append(f"{header}\n{names}")
    return "**Game signups (live from database)**\n\n" + "\n\n".join(blocks)


def remove_game_signup(ig_handle: str, game_id: Optional[int] = None) -> tuple[str, dict]:
    """
    Drop a member from a game and put the spot back.
    Returns ('removed'|'not_found'|'none', game).
    If game_id is None, remove from their newest signup.
    """
    handle = normalize_handle(ig_handle)
    if not handle:
        return "not_found", {}
    with get_conn() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS game_signups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                game_id INTEGER NOT NULL,
                ig_handle TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(game_id, ig_handle)
            )
            """
        )
        if game_id is not None:
            row = conn.execute(
                """
                SELECT s.id AS signup_id, g.id, g.when_text, g.location, g.spots
                FROM game_signups s
                JOIN games g ON g.id = s.game_id
                WHERE s.ig_handle = ? AND s.game_id = ?
                """,
                (handle, int(game_id)),
            ).fetchone()
        else:
            row = conn.execute(
                """
                SELECT s.id AS signup_id, g.id, g.when_text, g.location, g.spots
                FROM game_signups s
                JOIN games g ON g.id = s.game_id
                WHERE s.ig_handle = ?
                ORDER BY s.id DESC
                LIMIT 1
                """,
                (handle,),
            ).fetchone()
        if not row:
            if game_id is not None:
                return "not_found", {"id": int(game_id)}
            any_games = conn.execute("SELECT id FROM games LIMIT 1").fetchone()
            return ("none" if not any_games else "not_found"), {}
        row = _as_dict(row)
        conn.execute("DELETE FROM game_signups WHERE id = ?", (row["signup_id"],))
        conn.execute(
            "UPDATE games SET spots = spots + 1 WHERE id = ?",
            (row["id"],),
        )
        updated = conn.execute(
            "SELECT id, when_text, location, spots FROM games WHERE id = ?",
            (row["id"],),
        ).fetchone()
    return "removed", _as_dict(updated) if updated else row


def remove_signup_reply(status: str, handle: str, game: dict) -> str:
    at = f"@{normalize_handle(handle)}"
    when = (game or {}).get("when_text") or "that game"
    loc = (game or {}).get("location") or DEFAULT_GAME_LOCATION
    spots = (game or {}).get("spots")
    if status == "none":
        return "There is no game on the board right now."
    if status == "not_found":
        if game.get("id"):
            return f"**{at}** is not registered for game **#{game['id']}**."
        return f"**{at}** is not registered for any game."
    spot_bit = f" · **{spots}** spots left" if spots is not None else ""
    return (
        f"Removed **{at}** from **{when}** @ {loc}. "
        f"Spot is back on the board{spot_bit}."
    )


def maybe_game_invite(reply: str = "") -> str:
    """Sometimes append a soft invite to an upcoming game for eligible members."""
    games = [g for g in list_games() if int(g.get("spots") or 0) > 0]
    if not games:
        return ""
    lower = (reply or "").lower()
    if any(w in lower for w in ("join", "spot", "sign up", "come play", "want in", "upcoming")):
        return ""
    if random.random() > 0.38:
        return ""
    g = games[0]
    loc = g.get("location") or DEFAULT_GAME_LOCATION
    return (
        f"\n\nWant in on **{g['when_text']}** @ {loc}? "
        f"**{g['spots']}** spots left — say yes and I’ll hold one."
    )


def _last_assistant_text() -> str:
    messages = st.session_state.get("messages") or []
    prior = messages[:-1] if messages else []
    for msg in reversed(prior):
        if msg.get("role") == "assistant":
            return str(msg.get("content") or "")
    return ""


def _confirms_game_join(text: str, last_assistant: str) -> bool:
    raw = (text or "").strip()
    if not raw or len(raw) > 180:
        return False
    explicit = re.search(
        r"\b(join|joining|sign me up|count me in|i'?m in|im in|hold (a |one |my )?spot|want in|book me)\b",
        raw,
        re.I,
    )
    if explicit:
        return True
    short_yes = re.fullmatch(r"(yes|yeah|yep|yup|ok|okay|sure|in)[.!\s]*", raw, re.I)
    asked = re.search(r"want in|spots left|say yes|hold one", last_assistant or "", re.I)
    return bool(short_yes and asked)


def join_next_game(ig_handle: str) -> tuple[str, dict]:
    """
    Hold one spot for a gated-in member.
    Returns ('ok'|'already'|'full'|'none', game).
    """
    handle = normalize_handle(ig_handle)
    with get_conn() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS game_signups (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                game_id INTEGER NOT NULL,
                ig_handle TEXT NOT NULL,
                created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                admin_seen INTEGER NOT NULL DEFAULT 0,
                UNIQUE(game_id, ig_handle)
            )
            """
        )
        signup_cols = _pragma_signup_cols(conn)
        if "admin_seen" not in signup_cols:
            conn.execute(
                "ALTER TABLE game_signups ADD COLUMN admin_seen INTEGER NOT NULL DEFAULT 0"
            )
        games = conn.execute(
            """
            SELECT id, when_text, location, spots
            FROM games
            ORDER BY id DESC
            """
        ).fetchall()
        if not games:
            return "none", {}
        target = None
        for game in games:
            game = _as_dict(game)
            if int(game["spots"] or 0) > 0:
                target = game
                break
        if target is None:
            return "full", _as_dict(games[0])
        prior = conn.execute(
            """
            SELECT id FROM game_signups
            WHERE game_id = ? AND lower(ig_handle) = ?
            """,
            (target["id"], handle),
        ).fetchone()
        if prior:
            return "already", target
        cur = conn.execute(
            "UPDATE games SET spots = spots - 1 WHERE id = ? AND spots > 0",
            (target["id"],),
        )
        if cur.rowcount != 1:
            return "full", target
        conn.execute(
            "INSERT INTO game_signups (game_id, ig_handle, admin_seen) VALUES (?, ?, 0)",
            (target["id"], handle),
        )
        updated = conn.execute(
            "SELECT id, when_text, location, spots FROM games WHERE id = ?",
            (target["id"],),
        ).fetchone()
    return "ok", _as_dict(updated)


def game_join_reply(status: str, game: dict) -> str:
    when = (game or {}).get("when_text") or "the next session"
    loc = (game or {}).get("location") or DEFAULT_GAME_LOCATION
    wa = f"[Join the WhatsApp group]({WHATSAPP_GROUP_URL})"
    if status == "none":
        return "There is no game on the board right now."
    if status == "full":
        return f"**{when}** @ {loc} is full."
    if status == "already":
        return (
            f"You’re already in for **{when}** @ {loc}.\n\n"
            f"For logistics (court, timing, who’s coming), {wa}."
        )
    return (
        f"You’re in for **{when}** @ {loc}.\n\n"
        f"Tap in for logistics — court updates and who’s coming:\n{wa}"
    )


def is_admin(user: Optional[dict]) -> bool:
    if not user:
        return False
    return normalize_handle(user.get("ig_handle", "")) in ADMIN_HANDLES


def gate_override_for(ig_handle: str) -> Optional[bool]:
    """Admin lock: True = forced in, False = forced out, None = automatic."""
    user = get_user_by_handle(ig_handle)
    if not user or user.get("gate_override") is None:
        return None
    return bool(int(user["gate_override"]))


def apply_admin_gate(ig_handle: str, eligible: bool) -> bool:
    override = gate_override_for(ig_handle)
    return eligible if override is None else override


def set_user_gate(ig_handle: str, enabled: bool) -> Optional[dict]:
    """Force a handle in or out of club chat. Creates a row if they have not signed up yet."""
    handle = normalize_handle(ig_handle)
    if not handle or not re.match(r"^[A-Za-z0-9._]{2,30}$", handle):
        return None
    flag = 1 if enabled else 0
    with get_conn() as conn:
        existing = conn.execute(
            "SELECT id FROM users WHERE lower(ig_handle) = ?",
            (handle,),
        ).fetchone()
        if existing:
            conn.execute(
                """
                UPDATE users SET ai_enabled = ?, gate_override = ?, gate_detail = ? WHERE id = ?
                """,
                (
                    flag,
                    flag,
                    "Admin forced in. The automatic check is ignored."
                    if enabled
                    else "Admin forced out. The automatic check is ignored. The 25% roll does not apply.",
                    existing["id"],
                ),
            )
        else:
            conn.execute(
                """
                INSERT INTO users (ig_handle, pin_hash, ai_enabled, gate_override, gate_detail)
                VALUES (?, NULL, ?, ?, ?)
                """,
                (
                    handle,
                    flag,
                    flag,
                    "Admin forced in. The automatic check is ignored."
                    if enabled
                    else "Admin forced out. The automatic check is ignored. The 25% roll does not apply.",
                ),
            )
    return get_user_by_handle(handle)


def reset_user_pin(ig_handle: str, pin: str) -> Optional[dict]:
    handle = normalize_handle(ig_handle)
    if not handle or not re.fullmatch(r"\d{4}", pin or ""):
        return None
    user = get_user_by_handle(handle)
    if not user:
        return None
    with get_conn() as conn:
        conn.execute(
            "UPDATE users SET pin_hash = ? WHERE lower(ig_handle) = ?",
            (hash_pin(pin), handle),
        )
    return get_user_by_handle(handle)


def format_user_admin(user: dict) -> str:
    handle = user.get("ig_handle") or ""
    character = user.get("mascot") or user.get("animal") or "—"
    emoji = user.get("animal_emoji") or ""
    pin = "set" if user.get("pin_hash") else "not set"
    gate = "in" if user_ai_enabled(user) else "out"
    return (
        f"**@{handle}**\n"
        f"- Character: {character} {emoji}\n"
        f"- PIN: {pin}\n"
        f"- Gate: {gate}\n"
        f"- Gender: {user.get('gender') or '—'}\n"
        f"- Nationality: {user.get('nationality') or '—'}\n"
        f"- Age: {user.get('age_guess') or '—'}\n\n"
        f"**Why this gate**\n{gate_story_for_admin(user)}\n\n"
        f"**Why this character**\n{character_why_for_admin(user)}"
    )


def list_users(limit: int = 80) -> list[dict]:
    with get_conn() as conn:
        rows = conn.execute(
            """
            SELECT ig_handle, mascot, animal, animal_emoji, pin_hash,
                   ai_enabled, gender, age_guess, nationality
            FROM users
            ORDER BY lower(ig_handle) ASC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [_as_dict(r) for r in rows]


def users_as_context() -> str:
    users = list_users()
    if not users:
        return "No members in the database yet."
    lines: list[str] = []
    for u in users:
        handle = u.get("ig_handle") or "?"
        character = u.get("mascot") or u.get("animal") or "—"
        emoji = (u.get("animal_emoji") or "").strip()
        pin = "PIN" if u.get("pin_hash") else "no PIN"
        gate = "in" if user_ai_enabled(u) else "out"
        admin = " · admin" if normalize_handle(handle) in ADMIN_HANDLES else ""
        who = f"{character} {emoji}".strip()
        lines.append(f"- @{handle}{admin} — {who} · gate {gate} · {pin}")
    return f"**Members ({len(users)})**\n\n" + "\n".join(lines)


def maybe_lucky_in(ig_handle: str, eligible: bool) -> bool:
    """Failed automatic gate still gets in 25% of the time. Admin locks are final."""
    if eligible:
        return True
    if gate_override_for(ig_handle) is not None:
        return False
    return random.random() < 0.25


def character_reveal(name: str, emoji: str) -> str:
    who = f"**{name}** {emoji}".strip()
    return random.choice(
        [
            f"OMG. You got {who}.",
            f"Wait — {who}?! That’s your character.",
            f"Court just handed you {who}. Iconic.",
            f"No way. You’re {who}.",
        ]
    )


def admin_help_text() -> str:
    return (
        "**Admin commands**\n\n"
        "1. **Add a game** — `Add game Sat 3pm 4 spots`\n"
        f"   Needs a date, a time, and spots. Location defaults to **{DEFAULT_GAME_LOCATION}**.\n"
        "2. **Delete a game** — `delete game #3`\n"
        "   Removes the game and all its signups.\n"
        "3. **Add a user** — `add user @handle 4821`\n"
        "   Creates (or updates) a member with that PIN, gated in.\n"
        "4. **Delete a user** — `delete user @handle`\n"
        "   Removes the member and frees any held spots. Admin accounts are protected.\n"
        "5. **Gate in** — `gate in @handle`\n"
        "   Club chat, even if the automatic check would block them.\n"
        "6. **Gate out** — `gate out @handle`\n"
        "   Tennis stories only. No club chat.\n"
        "7. **User** — `user @handle`\n"
        "   Profile, why they are gated in or out (including the 25% roll), and why that character.\n"
        "8. **List users** — `list users` or `users`\n"
        "   All members with gate / character / PIN status.\n"
        "9. **Reset PIN** — `reset pin @handle 4821`\n"
        "   Sets a new 4-digit PIN.\n"
        "10. **Board** — `games`\n"
        "   List upcoming games.\n"
        "11. **Signups** — `signups`\n"
        "   Who registered for each game (@handles).\n"
        "12. **Remove signup** — `remove @handle` or `remove @handle from #3`\n"
        "   Drop them from a game and put the spot back.\n"
        "13. **Help** — `help` or `/help`\n"
        "14. **Log out** — `logout`\n\n"
        "_On Streamlit Cloud, add Turso secrets so deletes/signups survive reboots._"
    )


def try_admin_command(text: str) -> bool:
    """Handle admin-only chat commands. Returns True when the message was consumed."""
    raw = (text or "").strip()
    lower = raw.lower()
    if lower in {"help", "/help", "commands", "/commands"}:
        append_assistant(admin_help_text())
        return True
    if lower in {"games", "/games", "list games", "upcoming", "upcoming games"}:
        append_assistant(games_as_context())
        return True
    if lower in {
        "users",
        "/users",
        "list users",
        "list user",
        "list members",
        "members",
        "who",
    }:
        append_assistant(users_as_context())
        return True
    if lower in {
        "signups",
        "/signups",
        "who signed up",
        "registrations",
        "players",
        "who’s in",
        "who's in",
        "whos in",
    }:
        append_assistant(signups_as_context())
        return True
    del_game = re.fullmatch(
        r"(?:/)?(?:delete|remove)\s+game\s+#?(\d+)",
        raw,
        re.I,
    )
    if del_game:
        gid = int(del_game.group(1))
        ok, game = delete_game(gid)
        if not ok:
            append_assistant(f"No game **#{gid}** on the board.")
        else:
            when = game.get("when_text") or f"#{gid}"
            loc = game.get("location") or DEFAULT_GAME_LOCATION
            append_assistant(f"Deleted game **#{gid}** — {when} @ {loc}.")
        return True
    add_user = re.fullmatch(
        r"(?:/)?add\s+user\s+@?([A-Za-z0-9._]{2,30})\s+(\d{4})",
        raw,
        re.I,
    )
    if add_user:
        handle = normalize_handle(add_user.group(1))
        pin = add_user.group(2)
        status, user = admin_add_user(handle, pin)
        if status == "bad":
            append_assistant("Use `add user @handle 4821` with a valid handle and 4-digit PIN.")
        elif status == "created":
            append_assistant(
                f"Added **@{handle}** with PIN `{pin}`, gated **in**."
            )
        else:
            append_assistant(
                f"Updated **@{handle}** — PIN set to `{pin}`, gated **in**."
            )
        return True
    del_user = re.fullmatch(
        r"(?:/)?(?:delete|remove)\s+user\s+@?([A-Za-z0-9._]{2,30})",
        raw,
        re.I,
    )
    if del_user:
        handle = normalize_handle(del_user.group(1))
        status, user = admin_delete_user(handle)
        if status == "protected":
            append_assistant(f"**@{handle}** is an admin account and can’t be deleted.")
        elif status == "missing":
            append_assistant(f"No account for **@{handle}**.")
        else:
            append_assistant(f"Deleted **@{handle}**. Any held spots were put back.")
        return True
    drop = re.fullmatch(
        r"(?:/)?(?:remove|drop|unbook)\s+@?([A-Za-z0-9._]{2,30})"
        r"(?:\s+(?:from\s+)?(?:#|game\s*)?(\d+))?",
        raw,
        re.I,
    )
    if drop:
        handle = normalize_handle(drop.group(1))
        gid = int(drop.group(2)) if drop.group(2) else None
        status, game = remove_game_signup(handle, gid)
        append_assistant(remove_signup_reply(status, handle, game))
        return True
    who = re.fullmatch(r"(?:/)?(?:user|who|info|details)\s+@?([A-Za-z0-9._]{2,30})", raw, re.I)
    if who:
        handle = normalize_handle(who.group(1))
        user = get_user_by_handle(handle)
        if not user:
            append_assistant(f"No account for **@{handle}** yet.")
        else:
            append_assistant(format_user_admin(user))
        return True
    reset = re.fullmatch(
        r"(?:/)?reset\s+(?:pin|password)\s+@?([A-Za-z0-9._]{2,30})\s+(\d{4})",
        raw,
        re.I,
    )
    if reset:
        handle = normalize_handle(reset.group(1))
        pin = reset.group(2)
        user = reset_user_pin(handle, pin)
        if not user:
            append_assistant(f"Couldn’t reset **@{handle}**. Check the handle and use a 4-digit PIN.")
        else:
            append_assistant(f"PIN for **@{handle}** is now `{pin}`.")
        return True
    m = re.fullmatch(
        r"(?:/)?(?:gate|grant)\s+(in|out)\s+@?([A-Za-z0-9._]{2,30})",
        raw,
        re.I,
    )
    if not m:
        return False
    enabled = m.group(1).lower() == "in"
    handle = normalize_handle(m.group(2))
    user = set_user_gate(handle, enabled)
    if not user:
        append_assistant("That handle doesn’t look right. Try `gate in @name`.")
        return True
    at = f"@{handle}"
    if enabled:
        append_assistant(f"**{at}** is gated **in**. They get club chat on their next message.")
    else:
        append_assistant(f"**{at}** is gated **out**. They only get tennis stories.")
    return True


# ---------------------------------------------------------------------------
# Instagram scrape
# ---------------------------------------------------------------------------

_MOBILE_UA = (
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
    "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 "
    "Mobile/15E148 Safari/604.1"
)
_DESKTOP_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/122.0.0.0 Safari/537.36"
)


def _unescape_ig(value: str) -> str:
    if not value:
        return ""
    try:
        return json.loads(f'"{value}"')
    except Exception:
        return (
            value.replace("\\n", "\n")
            .replace("\\/", "/")
            .replace('\\"', '"')
            .encode("utf-8", "ignore")
            .decode("unicode_escape", errors="ignore")
        )


def _extract_from_html(html: str, handle: str) -> tuple[list[str], list[str]]:
    """Return (bits for model text, human-readable field lines)."""
    soup = BeautifulSoup(html, "html.parser")
    bits: list[str] = [f"instagram_handle:{handle}"]
    found: list[str] = []

    for key in (
        "og:title",
        "og:description",
        "og:image",
        "description",
        "twitter:title",
        "twitter:description",
        "twitter:image",
    ):
        tag = soup.find("meta", attrs={"property": key}) or soup.find("meta", attrs={"name": key})
        if tag and tag.get("content"):
            content = " ".join(tag["content"].strip().split())
            bits.append(content)
            found.append(f"{key}: {content[:200]}")

    if soup.title and soup.title.string:
        title = soup.title.string.strip()
        if title.lower() != "instagram":
            bits.append(title)
            found.append(f"title: {title[:200]}")

    # Embedded profile fields (mobile pages often include these in JS/JSON)
    for label, pattern in (
        ("full_name", r'"full_name"\s*:\s*"((?:\\.|[^"\\])*)"'),
        ("biography", r'"biography"\s*:\s*"((?:\\.|[^"\\])*)"'),
        ("username", r'"username"\s*:\s*"((?:\\.|[^"\\])*)"'),
        ("profile_pic_url_hd", r'"profile_pic_url_hd"\s*:\s*"((?:\\.|[^"\\])*)"'),
        ("profile_pic_url", r'"profile_pic_url"\s*:\s*"((?:\\.|[^"\\])*)"'),
    ):
        m = re.search(pattern, html)
        if m:
            val = _unescape_ig(m.group(1)).strip()
            if val:
                bits.append(f"{label}:{val}")
                found.append(f"{label}: {val[:200]}")

    priv = re.search(r'"is_private"\s*:\s*(true|false)', html, re.I)
    if priv:
        found.append(f"is_private: {priv.group(1).lower()}")
        bits.append(f"is_private:{priv.group(1).lower()}")

    # Follower counts from og/description style strings
    m_counts = re.search(
        r"([\d.,]+)\s*Followers?,\s*([\d.,]+)\s*Following,\s*([\d.,]+)\s*Posts?",
        html,
        re.I,
    )
    if m_counts:
        counts = (
            f"followers:{m_counts.group(1)} following:{m_counts.group(2)} "
            f"posts:{m_counts.group(3)}"
        )
        bits.append(counts)
        found.append(counts)

    # application/ld+json
    for s in soup.find_all("script", type="application/ld+json"):
        raw = (s.string or s.get_text() or "").strip()
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue
        if isinstance(data, dict):
            for key in ("name", "description", "alternateName"):
                if data.get(key):
                    val = str(data[key]).strip()
                    bits.append(val)
                    found.append(f"ld+json.{key}: {val[:200]}")
            img = data.get("image")
            if isinstance(img, str) and img.startswith("http"):
                found.append(f"ld+json.image: {img[:200]}")
            elif isinstance(img, dict) and img.get("url"):
                found.append(f"ld+json.image: {str(img['url'])[:200]}")

    # Large Relay JSON blobs sometimes carry biography without regex-friendly escapes
    for s in soup.find_all("script", attrs={"type": "application/json"}):
        raw = s.string or s.get_text() or ""
        if "biography" not in raw and "full_name" not in raw and "profile_pic" not in raw:
            continue
        for label in ("full_name", "biography", "profile_pic_url_hd", "profile_pic_url"):
            m = re.search(rf'"{label}"\s*:\s*"((?:\\.|[^"\\])*)"', raw)
            if m:
                val = _unescape_ig(m.group(1)).strip()
                if val and f"{label}:{val}" not in bits:
                    bits.append(f"{label}:{val}")
                    found.append(f"json.{label}: {val[:200]}")

    # Dedupe while preserving order
    bits = list(dict.fromkeys(b for b in bits if b))
    found = list(dict.fromkeys(f for f in found if f))
    return bits, found


def _clean_ig_media_url(url: str) -> str:
    url = _unescape_ig(url or "").strip().replace("&amp;", "&")
    return url.replace("\\u0026", "&").replace("\\/", "/")


def _usable_ig_media_url(url: str) -> bool:
    if not url.startswith("http"):
        return False
    # Truncated CDN links usually stop mid-query and fail with 403
    if ("scontent" in url or "fbcdn" in url or "cdninstagram" in url) and (
        "oh=" in url or "oe=" in url or len(url) > 280
    ):
        return True
    return len(url) > 40 and "http" in url


def _is_ig_brand_asset_url(url: str) -> bool:
    """True for Instagram chrome / logo / static pack assets — never feed posts."""
    low = (url or "").lower()
    if not low:
        return True
    markers = (
        "static.cdninstagram.com",
        "rsrc.php",
        "/static/",
        "/images/instagram/",
        "instagram.com/static",
        "ig_glyph",
        "glyph-logo",
        "instagram-logo",
        ".ico",
    )
    return any(m in low for m in markers)


def _is_placeholder_profile_url(url: str) -> bool:
    """Instagram's logged-out default silhouette, not a person's photo."""
    low = _clean_ig_media_url(url).lower()
    return "anonymous_profile" in low or "yw5vbnltb3vz" in low


def _chrome_get(url: str, headers: Optional[dict] = None, timeout: int = 20):
    """Browser-fingerprint GET. Falls back to requests if curl_cffi is missing or the TLS hop fails."""
    hdrs = dict(headers or {})
    try:
        from curl_cffi import requests as crequests

        try:
            return crequests.get(
                url,
                headers=hdrs,
                impersonate="chrome",
                timeout=timeout,
                allow_redirects=True,
            )
        except Exception:
            pass
    except ImportError:
        pass
    return requests.get(url, headers=hdrs, timeout=timeout, allow_redirects=True)


def _threads_profile_pic_urls(handle: str) -> tuple[list[str], str]:
    """
    Public Threads page for the same account.
    Instagram's own profile HTML is a login wall; Threads still embeds profile_pic_url.
    Returns (urls, state) where state is real | default_avatar | unavailable.
    """
    handle = normalize_handle(handle)
    if not handle:
        return [], "unavailable"
    try:
        resp = _chrome_get(
            f"https://www.threads.com/@{handle}",
            headers={
                "Accept": "text/html,application/xhtml+xml",
                "Accept-Language": "en-US,en;q=0.9",
            },
            timeout=max(SCRAPE_TIMEOUT, 18),
        )
    except Exception:
        return [], "unavailable"
    if getattr(resp, "status_code", 0) != 200 or not (getattr(resp, "text", "") or ""):
        return [], "unavailable"
    text = (resp.text or "").replace("\\u0026", "&").replace("\\/", "/").replace("&amp;", "&")
    found: list[str] = []
    for match in re.finditer(r'"profile_pic_url(?:_hd)?"\s*:\s*"(https://[^"]+)"', text):
        found.append(match.group(1))
    versions = re.search(r'"hd_profile_pic_versions"\s*:\s*\[(.*?)\]', text)
    if versions:
        for match in re.finditer(r'"url"\s*:\s*"(https://[^"]+)"', versions.group(1)):
            found.append(match.group(1))
    urls: list[str] = []
    for raw in found:
        url = _clean_ig_media_url(raw)
        if not _usable_ig_media_url(url) or _is_ig_brand_asset_url(url):
            continue
        if _is_placeholder_profile_url(url):
            continue
        if not re.search(r"t51\.\d+-19", url, re.I):
            continue
        urls.append(url)
    urls = list(dict.fromkeys(urls))
    if urls:
        return urls, "real"
    low = text.lower()
    if handle in low and ("anonymous_profile" in low or "yw5vbnltb3vz" in low):
        return [], "default_avatar"
    return [], "unavailable"


def _is_ig_feed_media_url(url: str) -> bool:
    """Accept only signed post/reel media CDN URLs (not profile avatars or brand assets)."""
    if not _usable_ig_media_url(url) or _is_ig_brand_asset_url(url):
        return False
    low = url.lower()
    # Profile-avatar CDN family
    if "t51.2885-19" in low:
        return False
    # Post / carousel / reel media families (t51.NNNN-15, t52.*, etc.)
    if re.search(r"t5[12]\.\d+-15", low):
        return True
    if ("scontent" in low or "fbcdn.net" in low) and (
        "ig_cache_key" in low or "dst-jpg" in low or "dst-jpegr" in low or "/v/t5" in low
    ):
        return True
    return False


def _node_is_pinned(node: dict) -> bool:
    """Profile-grid pins (and reel-tab pins) — usually the clearest face photos."""
    if not isinstance(node, dict):
        return False
    if node.get("is_pinned") or node.get("pinned"):
        return True
    for key in ("pinned_for_users", "timeline_pinned_user_ids", "clips_tab_pinned_user_ids"):
        pins = node.get(key)
        if isinstance(pins, list) and pins:
            return True
    return False


def _hd_pic_urls(user: dict) -> list[str]:
    """Widest profile photo first. Same order Instasaver uses: hd_profile_pic_url_info, then versions, then profile_pic_url_hd."""
    if not isinstance(user, dict):
        return []
    ranked: list[tuple[int, str]] = []
    hd = user.get("hd_profile_pic_url_info") or {}
    if isinstance(hd, dict):
        u = _clean_ig_media_url(str(hd.get("url") or ""))
        if _usable_ig_media_url(u):
            try:
                width = int(hd.get("width") or 1080)
            except (TypeError, ValueError):
                width = 1080
            ranked.append((width, u))
    versions = user.get("hd_profile_pic_versions") or []
    if isinstance(versions, list):
        for v in versions:
            if not isinstance(v, dict):
                continue
            u = _clean_ig_media_url(str(v.get("url") or ""))
            if not _usable_ig_media_url(u):
                continue
            try:
                width = int(v.get("width") or 0)
            except (TypeError, ValueError):
                width = 0
            ranked.append((width, u))
    for key, fallback_w in (("profile_pic_url_hd", 640), ("profile_pic_url", 150)):
        u = _clean_ig_media_url(str(user.get(key) or ""))
        if _usable_ig_media_url(u):
            ranked.append((fallback_w, u))
    ranked.sort(key=lambda item: item[0], reverse=True)
    return list(dict.fromkeys(u for _, u in ranked if not _is_placeholder_profile_url(u)))


def _node_media_urls(node: dict) -> list[str]:
    """Largest post image first, then other display URLs. Skips brand assets."""
    if not isinstance(node, dict):
        return []
    urls: list[str] = []
    versions = (node.get("image_versions2") or {}).get("candidates") or []
    if isinstance(versions, list):
        best_u = ""
        best_w = -1
        for cand in versions:
            if not isinstance(cand, dict):
                continue
            try:
                w = int(cand.get("width") or 0)
            except (TypeError, ValueError):
                w = 0
            cu = _clean_ig_media_url(str(cand.get("url") or ""))
            if _is_ig_feed_media_url(cu) and w >= best_w:
                best_w, best_u = w, cu
        if best_u:
            urls.append(best_u)
    resources = node.get("display_resources") or []
    if isinstance(resources, list):
        best_u = ""
        best_w = -1
        for res in resources:
            if not isinstance(res, dict):
                continue
            w = int(res.get("config_width") or res.get("width") or 0)
            ru = _clean_ig_media_url(str(res.get("src") or ""))
            if _is_ig_feed_media_url(ru) and w >= best_w:
                best_w, best_u = w, ru
        if best_u:
            urls.append(best_u)
    for key in ("display_url", "thumbnail_src", "thumbnail_url"):
        u = _clean_ig_media_url(str(node.get(key) or ""))
        if _is_ig_feed_media_url(u):
            urls.append(u)
    side = node.get("edge_sidecar_to_children") or {}
    for child in (side.get("edges") or [])[:2]:
        if isinstance(child, dict):
            urls.extend(_node_media_urls(child.get("node") or {}))
    return list(dict.fromkeys(urls))


def _looks_like_instagram_logo(raw: bytes) -> bool:
    """Reject downloaded IG glyph / gradient logo placeholders."""
    if not raw or len(raw) < 500:
        return True
    try:
        from io import BytesIO

        from PIL import Image, ImageStat

        im = Image.open(BytesIO(raw)).convert("RGB")
        w, h = im.size
        if w < 40 or h < 40:
            return True
        # Brand glyph is square; sample corners for purple→pink→orange gradient + bright lens
        if abs(w - h) > max(12, w // 10):
            return False
        pts = [
            im.getpixel((max(1, w // 20), max(1, h // 20))),
            im.getpixel((w - max(2, w // 20), max(1, h // 20))),
            im.getpixel((max(1, w // 20), h - max(2, h // 20))),
            im.getpixel((w - max(2, w // 20), h - max(2, h // 20))),
            im.getpixel((w // 2, h // 2)),
            im.getpixel((w // 2, max(1, h // 8))),
        ]
        purples = oranges = yellows = brights = 0
        for r, g, b in pts:
            if r > 210 and g > 210 and b > 210:
                brights += 1
            if r > 100 and b > 130 and g < 130:
                purples += 1
            if r > 180 and 70 < g < 160 and b < 110:
                oranges += 1
            if r > 200 and g > 160 and b < 120:
                yellows += 1
        if brights >= 1 and purples >= 1 and (oranges + yellows) >= 1:
            return True
        # Extra: very low-entropy gradient tiles are usually brand packs
        try:
            tiny = im.resize((32, 32))
            stat = ImageStat.Stat(tiny)
            if max(stat.stddev) < 18 and min(stat.mean) > 80:
                return True
        except Exception:
            pass
        return False
    except Exception:
        return False


def _profile_pic_candidates_from_html(html: str) -> list[str]:
    """Only this page's profile-picture fields. og:image is often a post, not the avatar."""
    html = html or ""
    found: list[str] = []
    patterns = (
        r'"profile_pic_url_hd"\s*:\s*"((?:\\.|[^"\\])*)"',
        r'"profile_pic_url"\s*:\s*"((?:\\.|[^"\\])*)"',
    )
    for pattern in patterns:
        m = re.search(pattern, html, re.I)
        if not m:
            continue
        url = _clean_ig_media_url(m.group(1))
        if _usable_ig_media_url(url) and re.search(r"t51\.\d+-19", url):
            found.append(url)
    return list(dict.fromkeys(found))


def _profile_pic_url_from_fields(fields: list[str], html: str = "") -> str:
    """Best single URL: HTML candidates first, then complete field lines."""
    cands = _profile_pic_candidates_from_html(html)
    if cands:
        return cands[0]
    preferred_prefixes = (
        "profile_pic_url_hd:",
        "json.profile_pic_url_hd:",
        "profile_pic_url:",
        "json.profile_pic_url:",
    )
    for prefix in preferred_prefixes:
        for f in fields:
            if f.startswith(prefix):
                url = _clean_ig_media_url(f[len(prefix) :].strip())
                if _usable_ig_media_url(url):
                    return url
    return ""


def _ig_user_id_from_html(html: str, handle: str) -> str:
    html = html or ""
    handle = normalize_handle(handle)
    patterns = (
        rf'profilePage_(\d+)',
        rf'"profile_id"\s*:\s*"(\d+)"',
        rf'"id"\s*:\s*"(\d+)"\s*,\s*"username"\s*:\s*"{re.escape(handle)}"',
        rf'"username"\s*:\s*"{re.escape(handle)}"\s*,\s*"id"\s*:\s*"(\d+)"',
    )
    for pat in patterns:
        m = re.search(pat, html, re.I)
        if m:
            return m.group(1)
    return ""


_ANDROID_IG_UA = (
    "Instagram 192.0.0.37.107 Android (31/12; 420dpi; 1080x2208; "
    "Google/google; Pixel 6; redfin; redfin; en_US; 302733750)"
)


def _fetch_instagram_user_api(handle: str, user_id: str = "", html: str = "") -> dict[str, Any]:
    """
    Pull web_profile_info / user info for HD photos, public feed thumbs, and richer fields.
    Returns {urls, feed_urls, fields, text_bits, user, ok}.
    """
    handle = normalize_handle(handle)
    out: dict[str, Any] = {
        "urls": [],
        "feed_urls": [],
        "pinned_urls": [],
        "fields": [],
        "text_bits": [],
        "user": {},
        "ok": False,
    }
    sess = requests.Session()
    sess.headers.update(
        {
            "User-Agent": _DESKTOP_UA,
            "Accept-Language": "en-US,en;q=0.9",
            "Accept": "*/*",
        }
    )
    # Warm cookies from the profile page (helps public HD endpoints)
    try:
        sess.get(
            f"https://www.instagram.com/{handle}/",
            headers={"Accept": "text/html", "Referer": "https://www.instagram.com/"},
            timeout=max(SCRAPE_TIMEOUT, 12),
            allow_redirects=True,
        )
    except requests.RequestException:
        pass

    csrf = sess.cookies.get("csrftoken")
    if csrf:
        sess.headers["X-CSRFToken"] = csrf

    def _collect_feed_from_user(user: dict) -> None:
        edge = user.get("edge_owner_to_timeline_media") or user.get("edge_media") or {}
        edges = edge.get("edges") if isinstance(edge, dict) else None
        if not isinstance(edges, list):
            return
        pinned: list[str] = []
        rest: list[str] = []
        for item in edges[:18]:
            if not isinstance(item, dict):
                continue
            node = item.get("node") or item
            if not isinstance(node, dict):
                continue
            urls = _node_media_urls(node)
            if _node_is_pinned(node):
                pinned.extend(urls)
            else:
                rest.extend(urls)
        out["pinned_urls"].extend(pinned)
        # Feed fills in only after pins; skip URLs already pinned
        seen = set(pinned)
        for u in rest:
            if u not in seen:
                out["feed_urls"].append(u)
                seen.add(u)

    def _absorb_user(user: dict) -> None:
        if not isinstance(user, dict) or not user:
            return
        out["user"] = user
        out["ok"] = True
        hd_urls = _hd_pic_urls(user)
        if hd_urls:
            out["hd_urls"] = list(dict.fromkeys(hd_urls + list(out.get("hd_urls") or [])))
            out["urls"] = list(dict.fromkeys(hd_urls + list(out.get("urls") or [])))
            out["fields"].append(f"hd_profile_sources:{len(hd_urls)}")
        uid_val = user.get("id") or user.get("pk")
        if uid_val:
            out["user_id"] = str(uid_val)

        bio = (user.get("biography") or "").strip()
        full = (user.get("full_name") or "").strip()
        uname = (user.get("username") or handle).strip()
        if full:
            out["fields"].append(f"full_name: {full[:200]}")
            out["text_bits"].append(f"full_name:{full}")
        if bio:
            out["fields"].append(f"biography: {bio[:400]}")
            out["text_bits"].append(f"biography:{bio}")
        if uname:
            out["fields"].append(f"username: {uname}")
        if "is_private" in user:
            out["fields"].append(f"is_private: {str(bool(user.get('is_private'))).lower()}")
            out["text_bits"].append(f"is_private:{str(bool(user.get('is_private'))).lower()}")
        for key, label in (
            ("category_name", "category"),
            ("business_category_name", "business_category"),
            ("public_email", "public_email"),
            ("public_phone_country_code", "phone_cc"),
            ("address_street", "address"),
            ("city_name", "city"),
            ("bio_links", "bio_links"),
        ):
            val = user.get(key)
            if val is None or val == "" or val == []:
                continue
            if key == "bio_links" and isinstance(val, list):
                titles = []
                for link in val[:5]:
                    if isinstance(link, dict):
                        titles.append(str(link.get("title") or link.get("url") or "")[:80])
                if titles:
                    out["fields"].append(f"bio_links: {', '.join(titles)}")
                    out["text_bits"].append("bio_links:" + ",".join(titles))
                continue
            out["fields"].append(f"{label}: {str(val)[:200]}")
            out["text_bits"].append(f"{label}:{val}")

        pronouns = user.get("pronouns")
        if pronouns:
            out["fields"].append(f"pronouns: {pronouns}")
            out["text_bits"].append(f"pronouns:{pronouns}")

        edge = user.get("edge_followed_by") or user.get("follower_count")
        if isinstance(edge, dict) and edge.get("count") is not None:
            out["fields"].append(f"followers:{edge.get('count')}")
        elif isinstance(edge, int):
            out["fields"].append(f"followers:{edge}")

        _collect_feed_from_user(user)

    # Prefer web_profile_info (public accounts often include HD + recent media here)
    try:
        resp = sess.get(
            f"https://www.instagram.com/api/v1/users/web_profile_info/?username={handle}",
            headers={
                "X-IG-App-ID": "936619743392459",
                "X-Requested-With": "XMLHttpRequest",
                "Referer": f"https://www.instagram.com/{handle}/",
            },
            timeout=max(SCRAPE_TIMEOUT, 14),
        )
        if resp.status_code == 200:
            user = ((resp.json() or {}).get("data") or {}).get("user") or {}
            _absorb_user(user)
    except Exception:
        pass

    uid = str(user_id or _ig_user_id_from_html(html, handle) or out.get("user_id") or "")
    if uid:
        try:
            resp = sess.get(
                f"https://i.instagram.com/api/v1/users/{uid}/info/",
                headers={
                    "User-Agent": _ANDROID_IG_UA,
                    "X-IG-App-ID": "567067343352427",
                },
                timeout=max(SCRAPE_TIMEOUT, 12),
            )
            if resp.status_code == 200:
                mobile_user = (resp.json() or {}).get("user") or {}
                hd_urls = _hd_pic_urls(mobile_user)
                if hd_urls:
                    out["hd_urls"] = list(dict.fromkeys(hd_urls + list(out.get("hd_urls") or [])))
                    out["urls"] = list(dict.fromkeys(hd_urls + list(out.get("urls") or [])))
                    out["fields"].append(f"mobile_hd_profile:{len(hd_urls)}")
                if not out["ok"] and mobile_user:
                    _absorb_user(mobile_user)
        except Exception:
            pass

    # HTML fallback for feed display URLs when API timeline empty
    if html and len(out["feed_urls"]) < 2:
        out["feed_urls"].extend(_feed_photo_urls_from_html(html))

    out["urls"] = [
        u for u in dict.fromkeys(out["urls"]) if not _is_placeholder_profile_url(u)
    ]
    if out.get("hd_urls"):
        out["hd_urls"] = [u for u in out["hd_urls"] if not _is_placeholder_profile_url(u)]
    # Instagram's profile HTML is a login wall. The public Threads page for the
    # same handle still includes the profile photo when one is set.
    if not out["urls"]:
        threads_urls, pic_state = _threads_profile_pic_urls(handle)
        out["fields"].append(f"profile_pic:{pic_state}")
        if threads_urls:
            out["hd_urls"] = list(dict.fromkeys(threads_urls + list(out.get("hd_urls") or [])))
            out["urls"] = list(threads_urls)
            out["fields"].append(f"threads_profile_pic:{len(threads_urls)}")
            out["ok"] = True
    out["pinned_urls"] = list(dict.fromkeys(out.get("pinned_urls") or []))[: PINNED_PHOTO_MAX * 2]
    out["feed_urls"] = [
        u for u in dict.fromkeys(out["feed_urls"]) if u not in set(out["pinned_urls"])
    ][: FEED_PHOTO_MAX * 2]
    out["fields"] = list(dict.fromkeys(out["fields"]))
    if out["feed_urls"]:
        out["fields"].append(f"feed_photo_candidates:{len(out['feed_urls'])}")
    if out["pinned_urls"]:
        out["fields"].append(f"pinned_photo_candidates:{len(out['pinned_urls'])}")
    return out


def _feed_photo_urls_from_html(html: str) -> list[str]:
    """Pull public timeline display/thumbnail URLs embedded in profile HTML."""
    html = html or ""
    found: list[str] = []
    patterns = (
        r'"display_url"\s*:\s*"((?:\\.|[^"\\])*)"',
        r'"thumbnail_src"\s*:\s*"((?:\\.|[^"\\])*)"',
        r'"thumbnail_url"\s*:\s*"((?:\\.|[^"\\])*)"',
        # Post media CDN family only (never static.cdninstagram brand packs)
        r'"(https:\\?/\\?/[^"]+(?:scontent|fbcdn)[^"]+t5[12]\.\d+-15[^"]+)"',
    )
    for pattern in patterns:
        for m in re.finditer(pattern, html, re.I):
            u = _clean_ig_media_url(m.group(1))
            if not _is_ig_feed_media_url(u):
                continue
            found.append(u)
            if len(found) >= FEED_PHOTO_MAX * 3:
                break
        if len(found) >= FEED_PHOTO_MAX * 2:
            break
    return list(dict.fromkeys(found))


def _fetch_ig_profile_pic_urls_api(handle: str, user_id: str = "", session: Optional[requests.Session] = None) -> list[str]:
    """Back-compat wrapper — HD URLs only."""
    data = _fetch_instagram_user_api(handle, user_id=user_id)
    return list(data.get("urls") or [])


def _ig_media_id(url: str) -> str:
    match = re.search(r"/(\d{8,})_", url or "")
    return match.group(1) if match else ""


def _is_profile_pic_cdn(url: str) -> bool:
    """Profile-picture files live on the t51-19 CDN. Posts are a different family."""
    return bool(re.search(r"t51\.\d+-19", url or ""))


def _pic_url_rank(url: str) -> int:
    """Higher means a larger signed rendition. A 150 thumb must stay under 640."""
    u = (url or "").lower()
    match = re.search(r"[sp](\d{2,4})x\d{2,4}", u)
    if match:
        score = int(match.group(1))
    elif re.search(r"t5[12]\.", u):
        score = 1200
    else:
        score = 0
    if "hd" in u:
        score += 40
    return score


def _upscale_profile_image(raw: bytes, min_side: int = 512) -> tuple[bytes, str]:
    """If IG only gave a tiny thumb, upscale for local storage/display quality."""
    try:
        from io import BytesIO

        from PIL import Image

        im = Image.open(BytesIO(raw))
        im = im.convert("RGB")
        w, h = im.size
        if max(w, h) >= min_side:
            buf = BytesIO()
            im.save(buf, format="JPEG", quality=92, optimize=True)
            return buf.getvalue(), "jpg"
        scale = min_side / float(max(w, h) or 1)
        new_size = (max(1, int(w * scale)), max(1, int(h * scale)))
        im = im.resize(new_size, Image.Resampling.LANCZOS)
        buf = BytesIO()
        im.save(buf, format="JPEG", quality=92, optimize=True)
        return buf.getvalue(), "jpg"
    except Exception:
        return raw, ""


def _pic_url_variants(url: str) -> list[str]:
    """Ask the CDN for the source size. Instasaver keeps the signed URL and swaps the stp size token (s150 → s1080)."""
    u = _clean_ig_media_url(url)
    if not u:
        return []
    out = [u]
    sizes = ("s1080x1080", "s640x640", "s320x320")
    for size in sizes:
        swapped = re.sub(r"[sp]\d{2,4}x\d{2,4}", size, u, count=1)
        if swapped != u:
            out.append(swapped)
        stp = re.sub(r"([?&]stp=[^&#]*?)s\d{2,4}x\d{2,4}", rf"\1{size}", u, count=1)
        if stp != u:
            out.append(stp)
    # Drop the size token so the CDN can return the encode named in efg (often profile_pic.www.1080).
    stripped = re.sub(r"([?&]stp=[^&#]*?)_s\d{2,4}x\d{2,4}", r"\1", u, count=1)
    if stripped != u:
        out.append(stripped)
    return list(dict.fromkeys(out))


def _image_side(raw: bytes) -> int:
    try:
        from io import BytesIO

        from PIL import Image

        im = Image.open(BytesIO(raw))
        w, h = im.size
        return max(int(w), int(h))
    except Exception:
        return 0


def _image_pixel_area(raw: bytes) -> int:
    try:
        from io import BytesIO

        from PIL import Image

        im = Image.open(BytesIO(raw))
        w, h = im.size
        return int(w) * int(h)
    except Exception:
        return len(raw or b"")


def _download_largest_image(urls: list[str], handle: str, priority: Optional[list[str]] = None) -> bytes:
    """Download candidates and keep the highest-resolution valid image."""
    best = b""
    best_side = 0
    headers_list = (
        {
            "User-Agent": _MOBILE_UA,
            "Accept": "image/avif,image/webp,image/apng,image/*,*/*;q=0.8",
            "Referer": f"https://www.instagram.com/{handle}/",
            "Origin": "https://www.instagram.com",
        },
        {
            "User-Agent": _ANDROID_IG_UA,
            "Accept": "*/*",
        },
        {
            "User-Agent": _DESKTOP_UA,
            "Accept": "image/avif,image/webp,image/*,*/*;q=0.8",
            "Referer": "https://www.instagram.com/",
        },
    )
    ordered: list[str] = []
    for url in list(priority or []) + sorted(dict.fromkeys(urls), key=_pic_url_rank, reverse=True):
        if url and url not in ordered:
            ordered.append(url)
    for url in ordered[:16]:
        if _is_placeholder_profile_url(url):
            continue
        for headers in headers_list:
            raw = b""
            try:
                resp = requests.get(
                    url, headers=headers, timeout=max(SCRAPE_TIMEOUT, 12), allow_redirects=True
                )
            except requests.RequestException:
                resp = None
            if resp is not None and resp.status_code == 200 and resp.content and len(resp.content) >= 200:
                ctype = (resp.headers.get("Content-Type") or "").lower()
                if not ctype or ctype.startswith("image/"):
                    raw = resp.content
            if not raw:
                try:
                    alt = _chrome_get(url, headers=headers, timeout=max(SCRAPE_TIMEOUT, 12))
                except Exception:
                    alt = None
                if alt is not None and getattr(alt, "status_code", 0) == 200 and alt.content and len(alt.content) >= 200:
                    ctype = (getattr(alt, "headers", {}) or {}).get("Content-Type") or ""
                    if not ctype or str(ctype).lower().startswith("image/"):
                        raw = alt.content
            if not raw:
                continue
            side = _image_side(raw)
            area = side * side if side else _image_pixel_area(raw)
            if area > best_side * best_side:
                best_side = side or int(area ** 0.5)
                best = raw
            break
        if best_side >= 1080:
            break
    return best


_INDOWN_CACHE: dict[str, dict[str, Any]] = {}


def _ig_page_missing(text: str) -> bool:
    low = (text or "").lower().replace("’", "'").replace("‘", "'")
    return any(
        phrase in low
        for phrase in (
            "sorry, this page isn't available",
            "the link you followed may be broken",
            "the page may have been removed",
        )
    )


def _indown_lookup(handle: str) -> dict[str, Any]:
    """
    Public profile card from the same form Indown uses.
    Missing accounts come back as 'User not found' with no profile block.
    Live accounts include the name, bio, follower count, and a full-size photo URL.
    """
    handle = normalize_handle(handle)
    empty: dict[str, Any] = {"ok": False, "missing": False, "urls": [], "fields": [], "text": "", "private": False}
    if not handle:
        return empty
    cached = _INDOWN_CACHE.get(handle)
    if cached:
        return cached
    try:
        from curl_cffi import requests as crequests

        sess = crequests.Session(impersonate="chrome")
    except Exception:
        sess = requests.Session()
        sess.headers["User-Agent"] = _DESKTOP_UA
    try:
        page = sess.get("https://indown.io/insta-dp-viewer/en1", timeout=max(SCRAPE_TIMEOUT, 20))
        html = getattr(page, "text", "") or ""
        token_m = re.search(r'name="_token" value="([^"]+)"', html)
        if getattr(page, "status_code", 0) != 200 or not token_m:
            return empty
        resp = sess.post(
            "https://indown.io/download",
            data={
                "referer": "https://indown.io/insta-dp-viewer/en1",
                "locale": "en",
                "_token": token_m.group(1),
                "link": f"https://www.instagram.com/{handle}/",
            },
            headers={
                "Referer": "https://indown.io/insta-dp-viewer/en1",
                "Origin": "https://indown.io",
            },
            timeout=max(SCRAPE_TIMEOUT, 30),
        )
    except Exception:
        return empty
    text = (getattr(resp, "text", "") or "").replace("&amp;", "&").replace("\\/", "/")
    name_m = re.search(r"<h3>([^<]+)</h3>", text)
    has_profile = 'id="result"' in text and bool(name_m)
    if not has_profile and "User not found" in text:
        out = {**empty, "missing": True, "ok": True}
        _INDOWN_CACHE[handle] = out
        return out
    if not has_profile:
        return empty
    bio_m = re.search(r'class="title">[^<]+</p>\s*<p>([^<]*)</p>', text)
    fol_m = re.search(r"Followers</th>\s*<td[^>]*>\s*([\d,]+)\s*</td>", text, re.I)
    priv_m = re.search(r"Private</th>\s*<td[^>]*>\s*([^<]+)\s*</td>", text, re.I)
    name = (name_m.group(1) if name_m else "").strip()
    bio = (bio_m.group(1) if bio_m else "").strip()
    followers = (fol_m.group(1) if fol_m else "").replace(",", "")
    private = (priv_m.group(1) if priv_m else "").strip().lower() in {"yes", "true", "private"}
    fields = []
    bits = []
    if name:
        fields.append(f"full_name: {name}")
        bits.append(f"full_name:{name}")
    if bio:
        fields.append(f"biography: {bio}")
        bits.append(f"biography:{bio}")
    if followers:
        fields.append(f"followers:{followers}")
        bits.append(f"followers:{followers}")
    fields.append(f"is_private: {'true' if private else 'false'}")
    result_html = text
    result_m = re.search(r'id="result"[\s\S]{0,12000}', text)
    if result_m:
        result_html = result_m.group(0)
    found = re.findall(r"https://[^\"'\s<>]+t51\.\d+-19[^\"'\s<>]+", result_html)
    urls: list[str] = []
    for raw in found:
        url = _clean_ig_media_url(raw.split("&dl=")[0])
        if not _usable_ig_media_url(url) or _is_placeholder_profile_url(url) or _is_ig_brand_asset_url(url):
            continue
        urls.append(url)
    urls.sort(key=lambda u: ("s150x150" in u or "s100x100" in u, "s320x320" in u))
    urls = list(dict.fromkeys(urls))
    first_id = _ig_media_id(urls[0]) if urls else ""
    if first_id:
        urls = [u for u in urls if _ig_media_id(u) == first_id]
    out = {
        "ok": True,
        "missing": False,
        "urls": list(dict.fromkeys(urls)),
        "fields": fields,
        "text": " | ".join(bits),
        "private": private,
    }
    _INDOWN_CACHE[handle] = out
    return out


def _indown_profile_pic_urls(handle: str) -> list[str]:
    """Full-size profile URL, including for private accounts."""
    return list(_indown_lookup(handle).get("urls") or [])


def download_ig_profile_photo(handle: str, photo_url: str = "", html: str = "", user_id: str = "", extra_urls: Optional[list[str]] = None) -> str:
    """Download best available IG profile photo into avatars/profiles/{handle}.jpg."""
    handle = normalize_handle(handle)
    if not handle:
        return ""
    os.makedirs(PROFILE_DIR, exist_ok=True)

    urls: list[str] = []
    if photo_url:
        urls.append(_clean_ig_media_url(photo_url))
    for u in extra_urls or []:
        urls.append(_clean_ig_media_url(u))
    for u in _profile_pic_candidates_from_html(html):
        urls.append(u)
    if not user_id and html:
        user_id = _ig_user_id_from_html(html, handle)
    # Callers that already fetched the API pass extra_urls (possibly empty). Don't hit Instagram twice.
    if extra_urls is None:
        api = _fetch_instagram_user_api(handle, user_id=user_id, html=html)
        for u in api.get("urls") or []:
            urls.append(_clean_ig_media_url(u))
    urls = [
        u
        for u in dict.fromkeys(urls)
        if _usable_ig_media_url(u)
        and _is_profile_pic_cdn(u)
        and not _is_ig_brand_asset_url(u)
        and not _is_placeholder_profile_url(u)
    ]
    anchor = ""
    for source in list(extra_urls or []) + ([photo_url] if photo_url else []):
        if _is_profile_pic_cdn(source) and _ig_media_id(source):
            anchor = _ig_media_id(source)
            break
    if anchor:
        urls = [u for u in urls if _ig_media_id(u) == anchor]
    urls.sort(key=_pic_url_rank, reverse=True)
    # Logged-out Instagram often signs only a 150px avatar. Indown can sign the
    # full file, but only when it is the same photo — never a post.
    indown_urls: list[str] = []
    if not urls or max(_pic_url_rank(u) for u in urls) < 640:
        for candidate in _indown_profile_pic_urls(handle):
            if not _is_profile_pic_cdn(candidate):
                continue
            if anchor and _ig_media_id(candidate) != anchor:
                continue
            indown_urls.append(candidate)
        urls = list(dict.fromkeys(indown_urls + urls))
    if not urls:
        return ""

    priority = [u for u in indown_urls if not anchor or _ig_media_id(u) == anchor]
    if not priority:
        priority = [u for u in urls if _ig_media_id(u) == anchor] if anchor else urls[:1]
    raw = _download_largest_image(urls, handle, priority=priority)
    if not raw or _looks_like_instagram_logo(raw):
        return ""

    # Keep the real pixels. Upscaling a 150px thumb made low-res look like HD.
    try:
        from io import BytesIO

        from PIL import Image

        im = Image.open(BytesIO(raw)).convert("RGB")
        buf = BytesIO()
        im.save(buf, format="JPEG", quality=92, optimize=True)
        raw2 = buf.getvalue()
        ext = "jpg"
    except Exception:
        raw2, ext = raw, "jpg"
    rel = f"profiles/{handle}.{ext}"
    dest = os.path.join(AVATAR_DIR, rel)
    try:
        with open(dest, "wb") as f:
            f.write(raw2)
    except OSError:
        return ""
    return rel if os.path.isfile(dest) else ""


def _post_shortcodes_from_html(html: str) -> list[str]:
    return list(dict.fromkeys(re.findall(r"/p/([A-Za-z0-9_-]{5,})/", html or "")))


def _embed_post_urls(shortcode: str) -> list[str]:
    """Signed post images from the public embed. Includes a real 1080 rendition."""
    code = (shortcode or "").strip()
    if not code:
        return []
    try:
        resp = _chrome_get(
            f"https://www.instagram.com/p/{code}/embed/captioned/",
            headers={
                "User-Agent": _DESKTOP_UA,
                "Accept-Language": "en-US,en;q=0.9",
            },
            timeout=max(SCRAPE_TIMEOUT, 20),
        )
        text = (getattr(resp, "text", "") or "").replace("\\u0026", "&").replace("\\/", "/").replace("&amp;", "&")
    except Exception:
        return []
    found = re.findall(r"https://[^\"'\s<>]+t5[12]\.\d+-15[^\"'\s<>]+", text)
    urls: list[str] = []
    for raw in found:
        url = _clean_ig_media_url(raw)
        if _is_ig_feed_media_url(url):
            urls.append(url)
    urls.sort(key=_pic_url_rank, reverse=True)
    return list(dict.fromkeys(urls))[:6]


def _hd_post_url_groups(html: str, limit: int) -> list[list[str]]:
    """One URL group per post, largest signed rendition first. No thumbnails."""
    groups: list[list[str]] = []
    for code in _post_shortcodes_from_html(html):
        if len(groups) >= limit:
            break
        urls = [u for u in _embed_post_urls(code) if _pic_url_rank(u) >= 640]
        if urls:
            groups.append(urls)
    return groups


def download_ig_feed_photos(
    handle: str,
    feed_urls: Optional[list[str]] = None,
    html: str = "",
    max_photos: int = FEED_PHOTO_MAX,
) -> list[str]:
    """
    Download up to max_photos public feed images into profiles/feed/{handle}_N.jpg.
    Returns relative paths under AVATAR_DIR.
    """
    handle = normalize_handle(handle)
    if not handle:
        return []
    feed_dir = os.path.join(PROFILE_DIR, "feed")
    os.makedirs(feed_dir, exist_ok=True)

    # Drop prior feed frames for this handle before writing fresh ones
    try:
        for name in os.listdir(feed_dir):
            if name.startswith(f"{handle}_"):
                try:
                    os.remove(os.path.join(feed_dir, name))
                except OSError:
                    pass
    except OSError:
        pass

    groups = _hd_post_url_groups(html, max_photos) if html else []
    if not groups:
        urls: list[str] = []
        for u in feed_urls or []:
            cu = _clean_ig_media_url(u)
            if _is_ig_feed_media_url(cu) and _pic_url_rank(cu) >= 640:
                urls.append(cu)
        if html:
            urls.extend(u for u in _feed_photo_urls_from_html(html) if _pic_url_rank(u) >= 640)
        if len(urls) < 2:
            api = _fetch_instagram_user_api(handle, html=html)
            urls.extend(u for u in (api.get("feed_urls") or []) if _is_ig_feed_media_url(u) and _pic_url_rank(u) >= 640)
        urls = list(dict.fromkeys(urls))
        urls.sort(key=_pic_url_rank, reverse=True)
        groups = [[u] for u in urls[:max_photos]]

    saved: list[str] = []
    for group in groups:
        if len(saved) >= max_photos:
            break
        raw = _download_largest_image(group[:4], handle)
        if not raw or len(raw) < 2_000 or _looks_like_instagram_logo(raw):
            continue
        if _image_side(raw) < 640:
            continue
        try:
            from io import BytesIO

            from PIL import Image

            im = Image.open(BytesIO(raw)).convert("RGB")
            buf = BytesIO()
            im.save(buf, format="JPEG", quality=92, optimize=True)
            raw2 = buf.getvalue()
        except Exception:
            raw2 = raw
        rel = f"profiles/feed/{handle}_{len(saved)}.jpg"
        dest = os.path.join(AVATAR_DIR, rel)
        try:
            with open(dest, "wb") as f:
                f.write(raw2)
        except OSError:
            continue
        if os.path.isfile(dest) and os.path.getsize(dest) >= 2_000 and _image_side(raw2) >= 640:
            saved.append(rel)
    return saved


def download_ig_pinned_photos(
    handle: str,
    pinned_urls: Optional[list[str]] = None,
    max_photos: int = PINNED_PHOTO_MAX,
) -> list[str]:
    """Download pinned profile posts into profiles/pins/{handle}_N.jpg."""
    handle = normalize_handle(handle)
    if not handle:
        return []
    pin_dir = os.path.join(PROFILE_DIR, "pins")
    os.makedirs(pin_dir, exist_ok=True)
    try:
        for name in os.listdir(pin_dir):
            if name.startswith(f"{handle}_"):
                try:
                    os.remove(os.path.join(pin_dir, name))
                except OSError:
                    pass
    except OSError:
        pass

    urls = [u for u in dict.fromkeys(pinned_urls or []) if _is_ig_feed_media_url(u)]
    urls.sort(key=_pic_url_rank, reverse=True)
    saved: list[str] = []
    for url in urls:
        if len(saved) >= max_photos:
            break
        raw = _download_largest_image([url], handle)
        if not raw or len(raw) < 2_000 or _looks_like_instagram_logo(raw):
            continue
        if _image_side(raw) < 640:
            continue
        try:
            from io import BytesIO

            from PIL import Image

            im = Image.open(BytesIO(raw)).convert("RGB")
            buf = BytesIO()
            im.save(buf, format="JPEG", quality=92, optimize=True)
            raw2 = buf.getvalue()
        except Exception:
            raw2 = raw
        rel = f"profiles/pins/{handle}_{len(saved)}.jpg"
        dest = os.path.join(AVATAR_DIR, rel)
        try:
            with open(dest, "wb") as f:
                f.write(raw2)
        except OSError:
            continue
        if os.path.isfile(dest) and os.path.getsize(dest) >= 2_000:
            saved.append(rel)
    return saved


def collect_ig_vision_photo_paths(
    handle: str,
    profile_path: str = "",
    feed_paths: Optional[list[str]] = None,
    pinned_paths: Optional[list[str]] = None,
) -> list[str]:
    """Pinned posts first (clearest face), then profile, then other feed frames."""
    ordered: list[str] = []

    def _add(rel: str) -> None:
        if not rel:
            return
        full = resolve_media_path(rel) if not os.path.isabs(rel) else rel
        if full and os.path.isfile(full) and full not in ordered:
            ordered.append(full)

    handle = normalize_handle(handle)
    for rel in pinned_paths or []:
        _add(rel)
    pin_dir = os.path.join(PROFILE_DIR, "pins")
    if handle and os.path.isdir(pin_dir):
        for name in sorted(os.listdir(pin_dir)):
            if name.startswith(f"{handle}_"):
                _add(os.path.join(pin_dir, name))
    _add(profile_path)
    for rel in feed_paths or []:
        _add(rel)
    return ordered[:VISION_MAX_IMAGES]


def set_user_ig_photo(ig_handle: str, ig_photo_path: str) -> None:
    handle = normalize_handle(ig_handle)
    if not handle or not ig_photo_path:
        return
    with get_conn() as conn:
        conn.execute(
            "UPDATE users SET ig_photo_path = ? WHERE lower(ig_handle) = ?",
            (ig_photo_path, handle),
        )


def ensure_ig_profile_photo(ig_handle: str, existing_path: str = "", force: bool = False) -> str:
    """Download + persist IG profile photo if missing/tiny. Does not re-assign animals."""
    handle = normalize_handle(ig_handle)
    if existing_path and resolve_media_path(existing_path) and not force:
        full = resolve_media_path(existing_path)
        # Refresh if previous save was a tiny CDN thumb
        try:
            meta = _image_file_meta(full)
            if (meta.get("width") or 0) >= 640 and os.path.getsize(full) >= 8_000:
                return existing_path
        except OSError:
            pass
    for ext in ("jpg", "jpeg", "png", "webp"):
        rel = f"profiles/{handle}.{ext}"
        full = resolve_media_path(rel)
        if full and not force:
            try:
                meta = _image_file_meta(full)
                if (meta.get("width") or 0) >= 640 and os.path.getsize(full) >= 8_000:
                    set_user_ig_photo(handle, rel)
                    return rel
            except OSError:
                pass

    try:
        scrape = scrape_instagram_bio(handle)
    except Exception:
        return existing_path or ""
    saved = scrape.get("ig_photo_path") or ""
    if saved:
        set_user_ig_photo(handle, saved)
    return saved


def _detect_visibility(html: str, fields: list[str], text: str) -> str:
    """Return public | private | unknown."""
    lower = (html or "").lower()
    joined = " ".join(fields).lower() + " " + (text or "").lower()
    if re.search(r'"is_private"\s*:\s*true', html or "", re.I) or "is_private: true" in joined:
        return "private"
    if "this account is private" in lower or "this account is private" in joined:
        return "private"
    if "this profile is private" in lower or "this profile is private" in joined:
        return "private"
    if re.search(r'"is_private"\s*:\s*false', html or "", re.I) or "is_private: false" in joined:
        return "public"
    # Rich public crumbs usually mean public profile
    has_bio = any(f.startswith("biography:") or f.startswith("json.biography:") for f in fields)
    has_counts = any(f.startswith("followers:") for f in fields)
    if has_bio or (has_counts and any(f.startswith("og:title:") for f in fields)):
        return "public"
    return "unknown"


def _use_installed_playwright_browsers() -> None:
    """Ignore a sandbox browser path when the real Playwright install is elsewhere."""
    forced = os.environ.get("PLAYWRIGHT_BROWSERS_PATH") or ""
    if not forced:
        return
    try:
        names = os.listdir(forced) if os.path.isdir(forced) else []
    except OSError:
        names = []
    if any(name.startswith("chromium") for name in names):
        return
    os.environ.pop("PLAYWRIGHT_BROWSERS_PATH", None)


def scrape_instagram_via_browser(handle: str) -> dict[str, Any]:
    """
    Playwright headless Chromium — bypasses simple login-wall HTML shells.
    Captures page HTML + web_profile_info JSON + image URLs for public profiles.
    """
    handle = normalize_handle(handle)
    out: dict[str, Any] = {
        "ok": False,
        "html": "",
        "fields": [],
        "text_bits": [],
        "urls": [],
        "feed_urls": [],
        "pinned_urls": [],
        "visibility": "unknown",
        "note": "",
        "ua_used": "playwright-chromium",
    }
    if not handle or not USE_BROWSER_IG:
        out["note"] = "browser IG disabled or bad handle"
        return out
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        out["note"] = "playwright not installed"
        return out
    _use_installed_playwright_browsers()

    api_user: dict[str, Any] = {}
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            # Desktop layout. Mobile is sent to the login page; the logged-out
            # desktop profile still shows the header photo, including on private accounts.
            context = browser.new_context(
                user_agent=_DESKTOP_UA,
                viewport={"width": 1280, "height": 900},
                locale="en-US",
                extra_http_headers={"Accept-Language": "en-US,en;q=0.9"},
            )
            page = context.new_page()

            def _on_response(resp: Any) -> None:
                nonlocal api_user
                try:
                    u = resp.url or ""
                    if "web_profile_info" in u and resp.status == 200:
                        data = resp.json()
                        user = ((data or {}).get("data") or {}).get("user") or {}
                        if isinstance(user, dict) and user:
                            api_user = user
                except Exception:
                    pass

            page.on("response", _on_response)
            url = f"https://www.instagram.com/{handle}/"
            page.goto(url, wait_until="domcontentloaded", timeout=45000)
            page.wait_for_timeout(2500)
            # Dismiss cookie / login soft walls when present
            for sel in (
                'button:has-text("Allow all cookies")',
                'button:has-text("Accept")',
                'button:has-text("Not Now")',
                'button:has-text("Decline optional cookies")',
                '[aria-label="Close"]',
            ):
                try:
                    loc = page.locator(sel).first
                    if loc.is_visible(timeout=800):
                        loc.click(timeout=800)
                        page.wait_for_timeout(500)
                except Exception:
                    pass
            page.wait_for_timeout(2000)
            # Explicitly pull web_profile_info with page cookies (HD + timeline)
            try:
                data = page.evaluate(
                    """async (username) => {
                        const r = await fetch(
                          `/api/v1/users/web_profile_info/?username=${username}`,
                          { headers: { 'X-IG-App-ID': '936619743392459', 'X-Requested-With': 'XMLHttpRequest' } }
                        );
                        if (!r.ok) return { _http: r.status };
                        return await r.json();
                    }""",
                    handle,
                )
                if isinstance(data, dict):
                    user = ((data.get("data") or {}).get("user")) or {}
                    if isinstance(user, dict) and user.get("username"):
                        api_user = user
            except Exception:
                pass

            # Nudge scroll to load grid thumbs
            try:
                page.mouse.wheel(0, 1200)
                page.wait_for_timeout(1500)
            except Exception:
                pass

            html = page.content() or ""
            out["html"] = html
            out["final_url"] = page.url

            # Collect img srcs from DOM. Pinned posts sit under a pin icon.
            try:
                pinned_srcs = page.evaluate(
                    """() => {
                        const out = [];
                        const icons = document.querySelectorAll('[aria-label*="Pinned" i], [aria-label*="pinned" i]');
                        icons.forEach((icon) => {
                          const card = icon.closest('a, article, div') || icon.parentElement;
                          const img = card && card.querySelector('img');
                          const src = img && (img.currentSrc || img.src);
                          if (src) out.push(src);
                        });
                        return out;
                    }"""
                )
            except Exception:
                pinned_srcs = []
            for src in pinned_srcs or []:
                u = _clean_ig_media_url(str(src))
                if _is_ig_feed_media_url(u):
                    out["pinned_urls"].append(u)

            try:
                imgs = page.eval_on_selector_all(
                    "img",
                    """els => els.map(e => ({
                        alt: e.alt || '',
                        src: e.currentSrc || e.src || ''
                    })).filter(e => e.src)""",
                )
            except Exception:
                imgs = []
            for item in imgs or []:
                if isinstance(item, str):
                    src, alt = item, ""
                else:
                    src = str((item or {}).get("src") or "")
                    alt = str((item or {}).get("alt") or "")
                u = _clean_ig_media_url(src)
                if not _usable_ig_media_url(u) or _is_ig_brand_asset_url(u) or _is_placeholder_profile_url(u):
                    continue
                alt_l = alt.lower()
                # Only this account's avatar. Other people on the page, and post
                # photos, also use Instagram image URLs and must not become the DP.
                if handle.lower() in alt_l and "profile picture" in alt_l:
                    out["urls"].append(u)
                elif _is_ig_feed_media_url(u):
                    out["feed_urls"].append(u)

            # Prefer grid article thumbs when present (more reliable than every <img>)
            try:
                grid = page.eval_on_selector_all(
                    "article img, main img, [role='main'] img",
                    "els => els.map(e => e.currentSrc || e.src).filter(Boolean)",
                )
            except Exception:
                grid = []
            for src in grid or []:
                u = _clean_ig_media_url(str(src))
                if _is_ig_feed_media_url(u):
                    out["feed_urls"].append(u)

            browser.close()
    except Exception as exc:
        out["note"] = f"playwright failed: {type(exc).__name__}: {exc}"
        return out

    # Absorb API user if intercepted
    if api_user:
        bio = (api_user.get("biography") or "").strip()
        full = (api_user.get("full_name") or "").strip()
        if full:
            out["fields"].append(f"full_name: {full[:200]}")
            out["text_bits"].append(f"full_name:{full}")
        if bio:
            out["fields"].append(f"biography: {bio[:400]}")
            out["text_bits"].append(f"biography:{bio}")
        if "is_private" in api_user:
            priv = bool(api_user.get("is_private"))
            out["fields"].append(f"is_private: {str(priv).lower()}")
            out["visibility"] = "private" if priv else "public"
        for key in ("profile_pic_url_hd", "profile_pic_url"):
            u = _clean_ig_media_url(str(api_user.get(key) or ""))
            if _usable_ig_media_url(u):
                out["urls"].append(u)
        edge = api_user.get("edge_owner_to_timeline_media") or {}
        pinned_set: list[str] = []
        rest: list[str] = []
        for item in (edge.get("edges") or [])[:18]:
            node = (item or {}).get("node") or {}
            urls = _node_media_urls(node)
            if _node_is_pinned(node):
                pinned_set.extend(urls)
            else:
                rest.extend(urls)
        out["pinned_urls"].extend(pinned_set)
        seen = set(out["pinned_urls"])
        for u in rest:
            if u not in seen:
                out["feed_urls"].append(u)
                seen.add(u)
        edge_f = api_user.get("edge_followed_by") or {}
        if isinstance(edge_f, dict) and edge_f.get("count") is not None:
            out["fields"].append(f"followers:{edge_f.get('count')}")
        out["ok"] = True
        out["note"] = "playwright captured web_profile_info"

    # Parse HTML crumbs as backup
    if html:
        try:
            bits, found = _extract_from_html(html, handle)
            for f in found:
                if f not in out["fields"]:
                    out["fields"].append(f)
            out["text_bits"].extend(bits[:20])
            out["feed_urls"].extend(_feed_photo_urls_from_html(html))
            out["urls"].extend(_profile_pic_candidates_from_html(html))
            if out["visibility"] == "unknown":
                out["visibility"] = _detect_visibility(html, out["fields"], " ".join(out["text_bits"]))
            if found or out["urls"]:
                out["ok"] = True
                if not out["note"]:
                    out["note"] = "playwright HTML scrape"
        except Exception:
            pass

    out["urls"] = list(dict.fromkeys(out["urls"]))
    out["pinned_urls"] = list(dict.fromkeys(out.get("pinned_urls") or []))[: PINNED_PHOTO_MAX * 2]
    out["feed_urls"] = [
        u for u in dict.fromkeys(out["feed_urls"]) if u not in set(out["pinned_urls"])
    ][: FEED_PHOTO_MAX * 2]
    out["fields"] = list(dict.fromkeys(out["fields"]))
    if not out["ok"] and not out["note"]:
        out["note"] = "playwright returned thin page"
    return out


def _merge_browser_into_scrape(result: dict[str, Any], browser: dict[str, Any], handle: str) -> dict[str, Any]:
    """Fold playwright results into the main scrape dict and download photos."""
    if not browser.get("ok") and not browser.get("html"):
        result["note"] = (result.get("note") or "") + f" Browser: {browser.get('note') or 'failed'}."
        return result

    for f in browser.get("fields") or []:
        if f not in (result.get("fields") or []):
            result.setdefault("fields", []).append(f)
    if browser.get("text_bits"):
        result["text"] = (
            (result.get("text") or "") + " | " + " | ".join(browser["text_bits"])
        )[:2400]
    if browser.get("visibility") and browser["visibility"] != "unknown":
        result["visibility"] = browser["visibility"]
    elif result.get("visibility") == "unknown":
        result["visibility"] = _detect_visibility(
            browser.get("html") or "",
            result.get("fields") or [],
            result.get("text") or "",
        )

    html = browser.get("html") or ""
    if _ig_page_missing(html):
        result["profile_missing"] = True
        result["status"] = "profile_missing"
        result["ok"] = False
        result["note"] = (result.get("note") or "") + " Instagram says this page isn't available."
        return result
    uid = _ig_user_id_from_html(html, handle) if html else ""
    pic_url = _profile_pic_url_from_fields(result.get("fields") or [], html)
    profile_urls = [u for u in (browser.get("urls") or []) if _is_profile_pic_cdn(u)]
    existing_meta = _image_file_meta(result.get("ig_photo_path") or "")
    low_res = (existing_meta.get("width") or 0) < 640
    if profile_urls or not result.get("ig_photo_path") or low_res:
        saved = download_ig_profile_photo(
            handle,
            photo_url=profile_urls[0] if profile_urls else pic_url,
            html="" if profile_urls else html,
            user_id=uid,
            extra_urls=profile_urls,
        )
        if saved:
            new_meta = _image_file_meta(saved)
            if not result.get("ig_photo_path") or (new_meta.get("width") or 0) >= (existing_meta.get("width") or 0):
                result["ig_photo_path"] = saved
                result["profile_photo_meta"] = new_meta
                result["profile_pic_url"] = pic_url

    if result.get("visibility") != "private":
        pinned = [u for u in (browser.get("pinned_urls") or []) if _is_ig_feed_media_url(u)]
        if pinned or not result.get("ig_pinned_paths"):
            pin_paths = download_ig_pinned_photos(handle, pinned_urls=pinned)
            if pin_paths or not result.get("ig_pinned_paths"):
                result["ig_pinned_paths"] = pin_paths
                result["pinned_photo_meta"] = [_image_file_meta(p) for p in pin_paths]
        browser_feeds = [u for u in (browser.get("feed_urls") or []) if _is_ig_feed_media_url(u)]
        # Refresh whenever browser found real post media, or we still have no feed
        if browser_feeds or not result.get("ig_feed_paths"):
            feed_paths = download_ig_feed_photos(
                handle,
                feed_urls=browser_feeds,
                html=html,
                max_photos=FEED_PHOTO_MAX,
            )
            if feed_paths or not result.get("ig_feed_paths"):
                result["ig_feed_paths"] = feed_paths
                result["feed_photo_meta"] = [_image_file_meta(p) for p in feed_paths]

    result["ok"] = bool(result.get("ok") or browser.get("ok") or result.get("ig_photo_path"))
    result["status"] = "browser_enriched" if result.get("ok") else result.get("status")
    result["ua_used"] = (result.get("ua_used") or "") + "+playwright"
    result["note"] = (result.get("note") or "") + f" {browser.get('note') or 'browser merge'}."
    result["browser"] = {
        "ok": browser.get("ok"),
        "urls": len(browser.get("urls") or []),
        "feed_urls": len(browser.get("feed_urls") or []),
        "note": browser.get("note"),
    }
    return result


def scrape_instagram_bio(
    ig_handle: str,
    *,
    pre_web: Optional[dict[str, Any]] = None,
    skip_web: bool = False,
) -> dict[str, Any]:
    """
    Public bio/meta scrape.
    Prefer calling research_handle_before_ig() first and pass pre_web.
    Falls back to Playwright browser when requests hit login wall / empty page.
    """
    handle = normalize_handle(ig_handle)
    url = f"https://www.instagram.com/{handle}/"
    result: dict[str, Any] = {
        "text": f"instagram_handle:{handle}",
        "ok": False,
        "status": "invalid_handle",
        "http_status": None,
        "url": url,
        "final_url": None,
        "fields": [],
        "note": "",
        "preview": "",
        "ua_used": None,
        "visibility": "unknown",
        "emojis": [],
        "web_search": None,
        "web_research": None,
        "profile_pic_url": "",
        "ig_photo_path": "",
        "ig_feed_paths": [],
        "profile_photo_meta": {},
        "feed_photo_meta": [],
    }

    if not handle or not re.match(r"^[A-Za-z0-9._]+$", handle):
        result["note"] = "Handle failed validation (letters, numbers, . _ only)."
        return result

    # Step 1 crumbs already done by caller — attach now
    if pre_web:
        result["web_research"] = pre_web
        web = pre_web.get("web") if isinstance(pre_web.get("web"), dict) else pre_web
        result["web_search"] = web
        if web.get("text"):
            result["text"] = f"{result['text']} | web:{web['text']}"[:2400]

    attempts = (
        ("mobile", _MOBILE_UA),
        ("desktop", _DESKTOP_UA),
    )
    last_error = ""
    best: dict[str, Any] | None = None

    for ua_name, ua in attempts:
        headers = {
            "User-Agent": ua,
            "Accept-Language": "en-US,en;q=0.9",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Referer": "https://www.instagram.com/",
        }
        try:
            resp = requests.get(url, headers=headers, timeout=SCRAPE_TIMEOUT, allow_redirects=True)
        except requests.RequestException as exc:
            last_error = f"{ua_name} request failed: {type(exc).__name__}: {exc}"
            continue

        final = (resp.url or "").lower()
        attempt = {
            "http_status": resp.status_code,
            "final_url": resp.url,
            "ua_used": ua_name,
            "html": resp.text,
        }

        if _ig_page_missing(resp.text or ""):
            result["profile_missing"] = True
            result["status"] = "profile_missing"
            result["ok"] = False
            result["note"] = "Instagram says this page isn't available."
            result["http_status"] = resp.status_code
            result["final_url"] = resp.url
            return result
        if "login" in final or "accounts/login" in final:
            last_error = f"{ua_name}: redirected to login wall"
            continue
        if resp.status_code != 200:
            last_error = f"{ua_name}: HTTP {resp.status_code}"
            continue

        try:
            bits, found = _extract_from_html(resp.text, handle)
        except Exception as exc:
            last_error = f"{ua_name}: parse failed ({type(exc).__name__})"
            continue

        scraped = " | ".join(bits)
        attempt.update(
            {
                "text": scraped[:1800],
                "fields": found,
                "preview": scraped[:400],
                "field_count": len(found),
            }
        )

        if best is None or attempt["field_count"] > best.get("field_count", 0):
            best = attempt

        useful = [f for f in found if not f.startswith("title: Instagram")]
        if any(f.startswith("biography:") or f.startswith("json.biography:") for f in found) or len(useful) >= 2:
            best = attempt
            break

    need_browser = False
    if not best:
        result["status"] = "request_error"
        result["note"] = last_error or "All fetch attempts failed."
        result["visibility"] = "unknown"
        need_browser = True
        if not result.get("web_search") and not skip_web:
            web = google_enrich_profile(handle)
            result["web_search"] = web
            if web.get("text"):
                result["text"] = f"{result['text']} | {web['text']}"[:1800]
                result["ok"] = True
                result["status"] = "web_fallback"
                result["note"] = "IG fetch failed; used web search crumbs."
        elif (result.get("web_search") or {}).get("text"):
            result["ok"] = True
            result["status"] = "web_fallback"
    else:
        result["http_status"] = best["http_status"]
        result["final_url"] = best["final_url"]
        result["ua_used"] = best["ua_used"]
        result["fields"] = best.get("fields") or []
        result["preview"] = best.get("preview") or ""
        base_text = best.get("text") or f"instagram_handle:{handle}"
        web_hit = result.get("web_search") or {}
        if web_hit.get("text"):
            result["text"] = f"{base_text} | web:{web_hit['text']}"[:2400]
        else:
            result["text"] = base_text
        result["visibility"] = _detect_visibility(best.get("html") or "", result["fields"], result["text"])
        result["emojis"] = _extract_profile_emojis(result["text"])

        useful = [f for f in result["fields"] if not f.startswith("title: Instagram")]
        if not useful:
            result["status"] = "empty_public_data"
            result["note"] = (
                "Page loaded, but almost no public meta/bio text was available "
                f"(tried mobile+desktop UA; last={last_error or 'n/a'})."
            )
            need_browser = True
        else:
            result["ok"] = True
            result["status"] = "ok"
            result["note"] = (
                f"Pulled {len(useful)} public field(s) using {best['ua_used']} Instagram page."
            )

        # Web enrichment if not already done in step 1
        if not result.get("web_search") and not skip_web:
            web = google_enrich_profile(handle)
            result["web_search"] = web
            if web.get("text"):
                result["text"] = f"{result['text']} | web:{web['text']}"[:2400]
                result["preview"] = (result["preview"] + " | " + web["text"])[:500]
                if not result["ok"]:
                    result["ok"] = True
                    result["status"] = "web_enriched"
                result["note"] = (result.get("note") or "") + " " + (web.get("note") or "")
                result["emojis"] = _extract_profile_emojis(result["text"])

        # API enrichment
        html = best.get("html") or ""
        uid = _ig_user_id_from_html(html, handle)
        api = _fetch_instagram_user_api(handle, user_id=uid, html=html)
        result["api_user"] = bool(api.get("ok"))
        if api.get("fields"):
            merged_fields = list(result.get("fields") or [])
            for f in api["fields"]:
                if f not in merged_fields:
                    merged_fields.append(f)
            result["fields"] = merged_fields
        if api.get("text_bits"):
            result["text"] = (result.get("text") or "") + " | " + " | ".join(api["text_bits"])
            result["text"] = result["text"][:2400]
            result["emojis"] = _extract_profile_emojis(result["text"])
            result["ok"] = True
            if result.get("status") in {"empty_public_data", "request_error"}:
                result["status"] = "api_enriched"
            result["visibility"] = _detect_visibility(html, result["fields"], result["text"])

        pic_url = _profile_pic_url_from_fields(result.get("fields") or [], html)
        result["profile_pic_url"] = pic_url
        saved = download_ig_profile_photo(
            handle,
            photo_url=pic_url,
            html=html,
            user_id=uid,
            extra_urls=list(api.get("hd_urls") or []) + list(api.get("urls") or []),
        )
        result["ig_photo_path"] = saved
        result["profile_photo_meta"] = _image_file_meta(saved) if saved else {}

        feed_paths: list[str] = []
        pin_paths: list[str] = []
        if result.get("visibility") == "private":
            result["note"] = (result.get("note") or "") + " Private account — profile pic + name only (no feed)."
        else:
            pin_paths = download_ig_pinned_photos(
                handle, pinned_urls=list(api.get("pinned_urls") or [])
            )
            feed_paths = download_ig_feed_photos(
                handle,
                feed_urls=list(api.get("feed_urls") or []),
                html=html,
                max_photos=FEED_PHOTO_MAX,
            )
            result["note"] = (result.get("note") or "") + (
                f" Public — profile + {len(pin_paths)} pinned + {len(feed_paths)} feed photo(s)."
            )
            if not feed_paths or not pin_paths:
                need_browser = True
            photo_side = int((result.get("profile_photo_meta") or {}).get("width") or 0)
            if photo_side and photo_side < 640:
                need_browser = True
        result["ig_pinned_paths"] = pin_paths
        result["pinned_photo_meta"] = [_image_file_meta(p) for p in pin_paths]
        result["ig_feed_paths"] = feed_paths
        result["feed_photo_meta"] = [_image_file_meta(p) for p in feed_paths]
        if feed_paths:
            result["fields"] = list(result.get("fields") or []) + [f"feed_photos_saved:{len(feed_paths)}"]
        if pin_paths:
            result["fields"] = list(result.get("fields") or []) + [f"pinned_photos_saved:{len(pin_paths)}"]

        if not saved and result.get("visibility") != "private":
            need_browser = True

    # HTML often hits the login wall. The profile-photo API can still return a picture.
    if not result.get("ig_photo_path"):
        api = _fetch_instagram_user_api(handle)
        saved = download_ig_profile_photo(
            handle,
            extra_urls=list(api.get("hd_urls") or []) + list(api.get("urls") or []),
            user_id=str(api.get("user_id") or ""),
        )
        if saved:
            result["ig_photo_path"] = saved
            result["profile_photo_meta"] = _image_file_meta(saved)
            result["ok"] = True
            result["note"] = (result.get("note") or "") + " Profile photo from the public profile."
            if result.get("status") in {None, "request_error", "invalid_handle", "web_fallback"}:
                result["status"] = "api_photo"
                need_browser = False
        elif api.get("ok"):
            result["note"] = (result.get("note") or "") + " IG API had no downloadable profile photo."

    # Logged-out desktop Instagram still shows the header photo on private accounts.
    # Threads often substitutes the gray silhouette for those, so that is not a reason to stop.
    if need_browser or (
        not result.get("ig_photo_path")
        and USE_BROWSER_IG
    ) or (
        not result.get("ig_feed_paths")
        and result.get("visibility") != "private"
        and USE_BROWSER_IG
    ):
        browser = scrape_instagram_via_browser(handle)
        result = _merge_browser_into_scrape(result, browser, handle)

    return _merge_indown_card(result, handle)


def _merge_indown_card(result: dict[str, Any], handle: str) -> dict[str, Any]:
    """
    Fold the public name, bio, follower count, and private flag into the scrape.
    A missing page stays missing so signup cannot invent a character from the handle.
    """
    if result.get("profile_missing"):
        return result
    card = _indown_lookup(handle)
    if card.get("missing"):
        result["profile_missing"] = True
        result["status"] = "profile_missing"
        result["ok"] = False
        result["note"] = (result.get("note") or "") + " Instagram has no page for this handle."
        return result
    if not card.get("ok"):
        return result
    for field in card.get("fields") or []:
        if field not in (result.get("fields") or []):
            result.setdefault("fields", []).append(field)
    if card.get("text"):
        result["text"] = ((result.get("text") or "") + " | " + card["text"])[:2400]
        for em in _extract_profile_emojis(card["text"]):
            if em not in result.setdefault("emojis", []):
                result["emojis"].append(em)
    if card.get("private"):
        result["visibility"] = "private"
    if card.get("urls") and not result.get("ig_photo_path"):
        saved = download_ig_profile_photo(handle, extra_urls=list(card["urls"]))
        if saved:
            result["ig_photo_path"] = saved
            result["profile_photo_meta"] = _image_file_meta(saved)
            result["ok"] = True
    return result


def _extract_profile_emojis(text: str) -> list[str]:
    found: list[str] = []
    for rule in EMOJI_AVATAR_RULES:
        for em in rule["emojis"]:
            if em in (text or "") and em not in found:
                found.append(em)
    return found


def _search_web_snippets(query: str, limit: int = 5) -> tuple[list[str], str]:
    """Return (snippets, source) from Google then DuckDuckGo."""
    headers = {
        "User-Agent": _DESKTOP_UA,
        "Accept-Language": "en-US,en;q=0.9",
        "Accept": "text/html",
    }
    snippets: list[str] = []
    source = ""

    try:
        gurl = f"https://www.google.com/search?q={quote_plus(query)}&hl=en&num=10"
        resp = requests.get(gurl, headers=headers, timeout=max(SCRAPE_TIMEOUT, 10))
        if resp.status_code == 200 and "detected unusual traffic" not in resp.text.lower():
            soup = BeautifulSoup(resp.text, "html.parser")
            for node in soup.select("div.BNeawe, span.aCOpRe, div.VwiC3b, div.kb0Qp, h3"):
                t = " ".join(node.get_text(" ", strip=True).split())
                if t and len(t) > 18:
                    snippets.append(t[:280])
                if len(snippets) >= limit:
                    break
            if snippets:
                source = "google"
    except requests.RequestException:
        pass

    if len(snippets) < 2:
        try:
            durl = f"https://html.duckduckgo.com/html/?q={quote_plus(query)}"
            resp = requests.get(durl, headers=headers, timeout=max(SCRAPE_TIMEOUT, 10))
            if resp.status_code == 200:
                soup = BeautifulSoup(resp.text, "html.parser")
                for node in soup.select("a.result__a, a.result__url, div.result__snippet"):
                    t = " ".join(node.get_text(" ", strip=True).split())
                    if t and len(t) > 15:
                        snippets.append(t[:280])
                    if len(snippets) >= limit:
                        break
                if snippets and not source:
                    source = "duckduckgo"
                elif snippets:
                    source = source or "duckduckgo"
        except requests.RequestException:
            pass

    # Bing HTML as third search source
    if len(snippets) < 2:
        try:
            burl = f"https://www.bing.com/search?q={quote_plus(query)}&setlang=en"
            resp = requests.get(burl, headers=headers, timeout=max(SCRAPE_TIMEOUT, 10))
            if resp.status_code == 200:
                soup = BeautifulSoup(resp.text, "html.parser")
                for node in soup.select("li.b_algo p, li.b_algo h2, .b_caption p"):
                    t = " ".join(node.get_text(" ", strip=True).split())
                    if t and len(t) > 18:
                        snippets.append(t[:280])
                    if len(snippets) >= limit:
                        break
                if snippets and source == "none":
                    source = "bing"
                elif snippets and "bing" not in source:
                    source = (source + "+bing") if source else "bing"
        except requests.RequestException:
            pass

    return list(dict.fromkeys(snippets))[:limit], source or "none"


def google_enrich_profile(handle: str) -> dict[str, Any]:
    """
    Public web crumbs for an IG handle (multi-query: IG + HK + foodie/KOL).
    Used BEFORE IG scrape when possible.
    """
    handle = normalize_handle(handle)
    queries = (
        f'"{handle}" OR @{handle} instagram',
        f'"{handle}" OR @{handle} (Hong Kong OR HK OR 香港 OR Taiwan OR Singapore)',
        f'"{handle}" OR @{handle} (foodie OR KOL OR influencer OR blogger OR 美食 OR 網紅)',
    )
    snippets: list[str] = []
    sources: list[str] = []
    for q in queries:
        got, src = _search_web_snippets(q, limit=4)
        for s in got:
            if s not in snippets:
                snippets.append(s)
        if src and src != "none":
            sources.append(src)
        if len(snippets) >= 10:
            break

    snippets = snippets[:10]
    source = "+".join(dict.fromkeys(sources)) if sources else "none"
    if not snippets:
        return {
            "ok": False,
            "source": source,
            "snippets": [],
            "text": "",
            "note": "Web search returned no useful public crumbs.",
            "is_kol": False,
            "kol_score": 0,
        }

    blob = " | ".join(snippets).lower()
    kol_keys = (
        "kol", "influencer", "blogger", "創作者", "網紅", "foodie", "美食",
        "followers", "萬追蹤", "k followers", "youtube", "xiaohongshu", "小紅書",
    )
    kol_hits = sum(1 for k in kol_keys if k in blob)
    is_kol = kol_hits >= 2 or ("kol" in blob and ("hong kong" in blob or "香港" in blob or "food" in blob))

    return {
        "ok": True,
        "source": source,
        "snippets": snippets,
        "text": " | ".join(snippets)[:1200],
        "note": f"Web research via {source} ({len(snippets)} snippet(s)"
        + ("; KOL cues" if is_kol else "")
        + ").",
        "is_kol": is_kol,
        "kol_score": kol_hits,
    }


def llm_research_profile_from_web(handle: str, web: dict[str, Any]) -> Optional[dict[str, Any]]:
    """
    DeepSeek text pass on web crumbs BEFORE IG — extract gender / locale / KOL niche.
    Example target: dinewithyy → female foodie KOL, Hong Kong, under 40.
    """
    client = get_client()
    if client is None:
        return None
    snippets = web.get("snippets") or []
    if not snippets and not (web.get("text") or ""):
        return None
    payload = {
        "handle": normalize_handle(handle),
        "web_snippets": snippets[:10],
        "web_text": (web.get("text") or "")[:1200],
        "web_kol_heuristic": bool(web.get("is_kol")),
    }
    prompt = (
        "You research a public Instagram creator from web search crumbs only (no login). "
        "Decide demographics and whether they are a KOL/influencer. "
        "Hong Kong foodie KOLs are common. Be decisive when crumbs are clear "
        "(e.g. dinewithyy-style foodie girl in HK). "
        "Return ONLY JSON:\n"
        "{"
        '"gender":"female|male|unknown",'
        '"nationality":"Hong Kong|Taiwan|China|Japan|Korea|Singapore|unknown|other",'
        '"age_guess":"age band or unknown",'
        '"is_kol":true,'
        '"kol_niche":"foodie|lifestyle|fashion|fitness|beauty|comedy|other|none",'
        '"display_name_guess":"",'
        '"confidence":0.0,'
        '"rationale":"one short sentence"'
        "}"
    )
    try:
        completion = client.chat.completions.create(
            model=active_model(),
            messages=[
                {"role": "system", "content": prompt},
                {"role": "user", "content": json.dumps(payload, ensure_ascii=False)},
            ],
            temperature=0.05,
            max_tokens=DEMO_MAX_TOKENS,
        )
        data = _parse_json_object(completion_text(completion))
        if not data:
            return None
        data["ok"] = True
        return data
    except Exception:
        return None


def _image_file_meta(path: str) -> dict[str, Any]:
    """Width/height/bytes for reporting whether we got full-res photos."""
    full = resolve_media_path(path) if path and not os.path.isabs(path) else path
    if not full or not os.path.isfile(full):
        return {"ok": False, "path": path or "", "bytes": 0, "width": 0, "height": 0, "hd": False}
    try:
        nbytes = os.path.getsize(full)
    except OSError:
        nbytes = 0
    w = h = 0
    try:
        from PIL import Image

        with Image.open(full) as im:
            w, h = im.size
    except Exception:
        pass
    side = max(w, h)
    return {
        "ok": True,
        "path": path,
        "bytes": nbytes,
        "width": w,
        "height": h,
        "hd": side >= 640 or nbytes >= 40_000,
        "full_res": side >= 900 or nbytes >= 80_000,
    }


def llm_prior_knowledge_handle(handle: str) -> Optional[dict[str, Any]]:
    """
    Ask DeepSeek what it already knows about @{handle} from public knowledge
    (covers KOLs like dinewithyy even when Google/DDG return nothing).
    """
    client = get_client()
    if client is None:
        return None
    prompt = (
        "You recall public Instagram / HK internet knowledge only. "
        f"Handle: @{normalize_handle(handle)}. "
        "If this is a known KOL/influencer/foodie/blogger (e.g. HK dining creators), say so. "
        "If you do not know them, set known=false and use unknown fields. "
        "Never invent private facts. Return ONLY JSON:\n"
        "{"
        '"known":true,'
        '"gender":"female|male|unknown",'
        '"nationality":"Hong Kong|Taiwan|China|Japan|Korea|Singapore|unknown|other",'
        '"age_guess":"age band or unknown",'
        '"is_kol":true,'
        '"kol_niche":"foodie|lifestyle|fashion|fitness|beauty|comedy|other|none",'
        '"display_name_guess":"",'
        '"followers_guess":0,'
        '"confidence":0.0,'
        '"rationale":"one short sentence"'
        "}"
    )
    try:
        completion = client.chat.completions.create(
            model=active_model(),
            messages=[
                {"role": "system", "content": "Extract public creator demographics as JSON only."},
                {"role": "user", "content": prompt},
            ],
            temperature=0.05,
            max_tokens=DEMO_MAX_TOKENS,
        )
        data = _parse_json_object(completion_text(completion))
        if not data:
            return None
        data["ok"] = True
        return data
    except Exception:
        return None


def research_handle_before_ig(handle: str) -> dict[str, Any]:
    """
    Step 1 of profile pipeline: internet search + DeepSeek before touching IG media.
    Falls back to DeepSeek prior knowledge when search is empty (KOL recall).
    """
    handle = normalize_handle(handle)
    web = google_enrich_profile(handle)
    llm = llm_research_profile_from_web(handle, web) if web.get("ok") else None
    prior = None
    if not (llm and str(llm.get("gender") or "unknown").lower() in ("female", "male")) or not (
        bool(web.get("is_kol")) or bool((llm or {}).get("is_kol"))
    ):
        prior = llm_prior_knowledge_handle(handle)

    # Merge: web-LLM first, then prior knowledge fills gaps / KOL
    gender = str((llm or {}).get("gender") or "unknown").lower()
    nationality = str((llm or {}).get("nationality") or "unknown")
    age_guess = str((llm or {}).get("age_guess") or "unknown")
    is_kol = bool(web.get("is_kol")) or bool((llm or {}).get("is_kol"))
    niche = str((llm or {}).get("kol_niche") or ("foodie" if is_kol else "none"))
    conf = float((llm or {}).get("confidence") or (0.4 if is_kol else 0.0))
    rationale = str((llm or {}).get("rationale") or web.get("note") or "")

    if prior and prior.get("ok") and prior.get("known"):
        if gender not in ("female", "male") and str(prior.get("gender") or "").lower() in ("female", "male"):
            gender = str(prior.get("gender")).lower()
            conf = max(conf, float(prior.get("confidence") or 0.55))
        if nationality.lower() in ("unknown", "", "other") and prior.get("nationality"):
            nationality = str(prior.get("nationality"))
        if age_guess.lower() == "unknown" and prior.get("age_guess"):
            age_guess = str(prior.get("age_guess"))
        if prior.get("is_kol"):
            is_kol = True
            if niche in ("none", "", "other") and prior.get("kol_niche"):
                niche = str(prior.get("kol_niche"))
            conf = max(conf, float(prior.get("confidence") or 0.6))
        if prior.get("rationale"):
            rationale = (rationale + "; " if rationale else "") + f"prior: {prior.get('rationale')}"

    # Seeded creator card (last resort when search engines / model recall fail)
    seed = _KNOWN_CREATORS.get(handle)
    if seed and (
        gender not in ("female", "male")
        or nationality.lower() in ("unknown", "", "other")
        or (seed.get("is_kol") and not is_kol)
    ):
        if gender not in ("female", "male"):
            gender = str(seed.get("gender") or gender)
        if nationality.lower() in ("unknown", "", "other"):
            nationality = str(seed.get("nationality") or nationality)
        if age_guess.lower() == "unknown" and seed.get("age_guess"):
            age_guess = str(seed.get("age_guess"))
        if seed.get("is_kol"):
            is_kol = True
            niche = str(seed.get("kol_niche") or niche)
        conf = max(conf, float(seed.get("confidence") or 0.75))
        rationale = (rationale + "; " if rationale else "") + f"seed: {seed.get('rationale')}"

    out = {
        "ok": bool(
            web.get("ok")
            or (llm and llm.get("ok"))
            or (prior and prior.get("ok"))
            or bool(seed)
        ),
        "web": web,
        "llm": llm or {},
        "prior": prior or {},
        "seed": seed or {},
        "is_kol": is_kol,
        "kol_niche": niche,
        "gender": gender,
        "nationality": nationality,
        "age_guess": age_guess,
        "confidence": conf,
        "rationale": rationale,
        "note": web.get("note") or "",
    }
    return out


def format_scrape_report(handle: str, scrape: dict[str, Any]) -> str:
    """Human-readable scrape debug block for chat."""
    vis = scrape.get("visibility") or "unknown"
    lines = [
        "### IG scrape report",
        f"- Handle: `@{handle}`",
        f"- Visibility: **{vis}**",
        f"- URL: {scrape.get('url')}",
        f"- HTTP: `{scrape.get('http_status')}`",
        f"- Status: **{scrape.get('status')}**",
        f"- Note: {scrape.get('note') or '—'}",
    ]
    emos = scrape.get("emojis") or []
    if emos:
        lines.append(f"- Bio emojis spotted: {' '.join(emos)}")
    web = scrape.get("web_search") or {}
    if web:
        lines.append(f"- Web search: `{web.get('source')}` — {web.get('note') or '—'}")
        for s in (web.get("snippets") or [])[:3]:
            lines.append(f"  - {s}")
    fields = scrape.get("fields") or []
    if fields:
        lines.append("- Fields found:")
        for f in fields[:8]:
            lines.append(f"  - {f}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# DeepSeek
# ---------------------------------------------------------------------------


def get_client() -> Optional[OpenAI]:
    # Always reload .env so Streamlit picks up key/base/model without a full OS env
    try:
        from dotenv import load_dotenv

        load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"), override=True)
    except ImportError:
        pass

    key = (os.environ.get("DEEPSEEK_API_KEY") or "").strip()
    base = (os.environ.get("DEEPSEEK_BASE_URL") or DEEPSEEK_BASE_URL).strip().rstrip("/")
    model = (os.environ.get("DEEPSEEK_MODEL") or DEEPSEEK_MODEL).strip()
    try:
        key = key or str(st.secrets.get("DEEPSEEK_API_KEY", "") or "").strip()
        base = (str(st.secrets.get("DEEPSEEK_BASE_URL", "") or "").strip() or base).rstrip("/")
        model = str(st.secrets.get("DEEPSEEK_MODEL", "") or "").strip() or model
    except Exception:
        pass
    if not key:
        return None
    # Cache active model for create() callers
    st.session_state["_api_model"] = model
    st.session_state["_api_base"] = base
    return OpenAI(api_key=key, base_url=base)


def active_model() -> str:
    return (
        st.session_state.get("_api_model")
        or os.environ.get("DEEPSEEK_MODEL")
        or DEEPSEEK_MODEL
    )


def _bio_nickname_from_scraped(scraped: str) -> str:
    """Prefer a short bio nickname (e.g. 一粒餓豆 before 'HK Foodie…')."""
    text = scraped or ""
    bio = ""
    m = re.search(r"biography:\s*(.+?)(?:\s*\|\s*[a-z_]+:|\s*$)", text, re.I | re.S)
    if m:
        bio = m.group(1).strip()
    if not bio:
        m2 = re.search(r'on Instagram:\s*"([^"]+)"', text, re.I)
        if m2:
            bio = m2.group(1).strip()
    if not bio:
        return ""

    # Normalize separators; IG often flattens newlines into spaces
    bio = bio.replace("\r", "\n")
    first = re.split(r"[\n|]+", bio)[0].strip().strip('"“”')
    if not first:
        return ""

    # Leading CJK nickname (common IG style: 一粒餓豆 HK Foodie…)
    cjk = re.match(r"^([\u4e00-\u9fff々〆〇]{2,12})", first)
    if cjk:
        return cjk.group(1)

    # Short first token / short whole line — skip emoji-only "names"
    def _usable_nick(s: str) -> bool:
        s = (s or "").strip()
        if not s or len(s) > 16:
            return False
        if s.lower().startswith("http"):
            return False
        # Reject pure emoji / symbol tokens (e.g. 🐱 alone)
        letters = re.sub(r"[^\w\u4e00-\u9fff]", "", s, flags=re.UNICODE)
        return bool(letters)

    token = first.split()[0].strip("本人·•-–—|/") if first.split() else ""
    if _usable_nick(token) and len(token) <= 12:
        return token
    if _usable_nick(first):
        return first
    return ""


def _looks_foodie(text: str) -> bool:
    t = (text or "").lower()
    keys = (
        "foodie", "sushi", "ramen", "coffee", "cafe", "dessert", "tea",
        "下午茶", "美食", "餓", "吃", "finedine", "afternoontea",
    )
    return any(k in t for k in keys)


def _score_avatar(pool_item: dict[str, Any], blob_lower: str, raw_text: str) -> tuple[int, list[str]]:
    """Return (score, evidence bullets)."""
    score = 0
    evidence: list[str] = []
    file_name = pool_item["file"]

    # Emoji rules get priority
    for rule in EMOJI_AVATAR_RULES:
        hit = [em for em in rule["emojis"] if em in (raw_text or "")]
        if not hit:
            continue
        if file_name in rule["files"]:
            score += int(rule["boost"])
            evidence.append(f"emoji {''.join(hit)} → {rule['reason']} (+{rule['boost']})")

    for tag in pool_item.get("tags") or []:
        # Emoji tags must match exactly in raw text; word tags use lowercase blob
        if len(tag) <= 2 and not tag.isascii():
            # short CJK
            if tag in (raw_text or "") or tag.lower() in blob_lower:
                score += 3
                evidence.append(f"keyword “{tag}”")
        elif tag in (raw_text or ""):  # emoji tag
            score += 3
            evidence.append(f"tag “{tag}”")
        elif tag.lower() in blob_lower:
            bump = 2 if len(tag) > 3 else 1
            score += bump
            evidence.append(f"keyword “{tag}” (+{bump})")

    # Deduplicate evidence while keeping order
    evidence = list(dict.fromkeys(evidence))
    return score, evidence


def _match_avatar_from_profile(scraped: str, handle: str) -> tuple[dict[str, Any], int, str, list[str]]:
    """Pick a pre-generated avatar; return avatar, score, reason, evidence list."""
    raw = scraped or ""
    blob = f"{raw} {handle}".lower()
    available = [p for p in AVATAR_POOL if os.path.isfile(os.path.join(AVATAR_DIR, p["file"]))]
    if not available:
        available = list(AVATAR_POOL)

    scored: list[tuple[int, dict[str, Any], list[str]]] = []
    for p in available:
        sc, ev = _score_avatar(p, blob, raw)
        scored.append((sc, p, ev))
    scored.sort(key=lambda x: (-x[0], x[1]["file"]))
    best_score, best, evidence = scored[0]

    if best_score <= 0:
        best = available[abs(hash(handle)) % len(available)]
        best_score = 0
        reason = "wildcard pick (no strong bio/emoji signal)"
        evidence = ["no keyword/emoji hits — hashed handle into the pool"]
        return best, best_score, reason, evidence

    # Prefer cat portraits hard when cat/butterfly emoji present
    cat_emoji_hit = any(em in raw for em in ["🐱", "🐈", "😺", "😸", "😻", "🦋", "🐈‍⬛"])
    if cat_emoji_hit and best["file"] not in {
        "fat_cat.png", "foodie_cat.png", "dumpling_cat.png", "crosscourt_cat.png"
    }:
        for sc, p, ev in scored:
            if p["file"] in {"fat_cat.png", "foodie_cat.png", "dumpling_cat.png", "crosscourt_cat.png"} and sc > 0:
                best, best_score, evidence = p, sc, ev
                break

    if any("emoji" in e for e in evidence):
        raw_reason = next((e.split("→", 1)[-1].strip() for e in evidence if "emoji" in e), "emoji match")
        reason = re.sub(r"\s*\(\+\d+\)\s*$", "", raw_reason).strip()
    elif any(t in blob for t in ("cat", "貓")) and _looks_foodie(blob):
        reason = "cat lover + foodie keywords"
    elif any(t in blob for t in ("travel", "traveller", "旅")):
        reason = "travel keywords in bio/web crumbs"
    else:
        reason = f"best keyword fit for “{best['label']}”"

    return best, best_score, reason, evidence[:8]


def _humor_assign_block(
    handle: str,
    display_name: str,
    avatar: dict[str, Any],
    reason: str,
    score: int,
    evidence: list[str],
    visibility: str,
    scrape: Optional[dict[str, Any]] = None,
) -> str:
    label = avatar["label"]
    emo = avatar.get("emoji") or "🎾"
    vis = visibility or "unknown"
    vis_line = {
        "public": "IG visibility: **public**",
        "private": "IG visibility: **private**",
        "unknown": "IG visibility: **unknown** (couldn’t confirm)",
    }.get(vis, f"IG visibility: **{vis}**")

    if score >= 8:
        lead = (
            f"Hey @{handle} — strong signal: {reason}. "
            f"Here’s a **{label}** for you, **{display_name}** {emo}"
        )
    elif score >= 3:
        lead = (
            f"Hey @{handle} — solid match ({reason}). "
            f"Meet your **{label}**, **{display_name}** {emo}"
        )
    elif score >= 1:
        lead = (
            f"Hey @{handle} — soft match ({reason}). "
            f"Drafted you a **{label}**, **{display_name}** {emo}"
        )
    else:
        lead = (
            f"Hey @{handle} — no loud bio signal, so wildcard pick: "
            f"**{label}** for **{display_name}** {emo}"
        )

    why_lines = [f"- {e}" for e in evidence] or ["- general court vibes / handle hash"]
    block = (
        f"{lead}\n\n"
        f"{vis_line}\n\n"
        f"**Why {label}?**\n"
        + "\n".join(why_lines)
        + f"\n- match score: `{score}`"
    )

    web = (scrape or {}).get("web_search") or {}
    if vis == "private":
        if web.get("ok"):
            block += (
                f"\n\nPrivate account — ran a web search (`{web.get('source')}`) and used public crumbs:"
            )
            for s in (web.get("snippets") or [])[:3]:
                block += f"\n- {s}"
        else:
            block += "\n\nPrivate account — web search didn’t add much, so matching used whatever IG still exposed."
    elif web.get("ok") and scrape and scrape.get("status") in {"web_enriched", "web_fallback", "empty_public_data"}:
        block += f"\n\nAlso peeked at `{web.get('source')}` results to thicken the signal."

    emos = (scrape or {}).get("emojis") or []
    if emos:
        block += f"\n\nBio emojis noticed: {' '.join(emos)}"

    return block


def assign_animal_and_vibe(
    ig_handle: str,
    scraped: str,
    scrape: Optional[dict[str, Any]] = None,
) -> tuple[str, str, str, str, str]:
    """
    Fast local assign from the pre-generated 40-photo pool.
    Returns (display_name, vibe, emoji, mascot_label, avatar_path).
    """
    handle = normalize_handle(ig_handle)
    bio_nick = _bio_nickname_from_scraped(scraped)
    vision = (scrape or {}).get("vision") if isinstance((scrape or {}).get("vision"), dict) else {}
    photo_blob = str((vision or {}).get("match_blob") or "")
    avatar, score, reason, evidence = _match_avatar_from_profile(
        f"{scraped}\n{photo_blob}".strip(),
        handle,
    )
    emoji = avatar.get("emoji") or "🎾"
    avatar_path = avatar["file"]
    mascot = avatar.get("label") or avatar_path
    # Prefer real nickname; never store emoji-only as the animal name
    display_name = bio_nick or mascot or handle
    why_lines = [f"{mascot}: {reason}"]
    if isinstance(scrape, dict):
        fields = list(scrape.get("fields") or [])
        name = _field_value(fields, "full_name:")
        bio = _field_value(fields, "biography:")
        followers = _field_value(fields, "followers:")
        if name:
            why_lines.append(f"- Name: {name}")
        if bio:
            why_lines.append(f"- Bio: {bio}")
        if followers:
            why_lines.append(f"- Followers: {followers}")
    for item in evidence[:6]:
        why_lines.append(f"- {item}")
    why_lines.append(f"Match score: {score}")
    if isinstance(scrape, dict):
        scrape["assign_why"] = "\n".join(why_lines)
    visibility = (scrape or {}).get("visibility") or "unknown"
    vibe = _humor_assign_block(
        handle, display_name, avatar, reason, score, evidence, visibility, scrape
    )
    return display_name, vibe, emoji, mascot, avatar_path


def _field_value(fields: list[str], *prefixes: str) -> str:
    for prefix in prefixes:
        for f in fields or []:
            if f.startswith(prefix):
                return f[len(prefix) :].strip()
    return ""


def _strip_name_noise(name: str) -> str:
    """Drop leading emoji/symbols so “🦄 Lisa Sum” → Lisa Sum."""
    s = (name or "").strip()
    s = re.sub(
        r"^[\s\W_🦄🌸🎀👰🤵❤️💖✨🌟💫⭐️👩👧💃💅👗💄👑💍🎉🎊💕💗💓💞💘💝]+",
        "",
        s,
        flags=re.U,
    ).strip()
    s = re.sub(r"[\|·•]+.*$", "", s).strip()
    return s


def _split_embedded_surname(word: str) -> tuple[str, str]:
    """MINTYWONG → (Minty, Wong) when ending matches a CJK surname."""
    w = (word or "").strip()
    low = w.lower()
    for sur in sorted(_CJK_SURNAMES, key=len, reverse=True):
        if len(sur) < 2:
            continue
        if low.endswith(sur) and len(low) > len(sur) + 2:
            given = w[: -len(sur)]
            surname = w[-len(sur) :]
            return given.title(), surname.title()
    return w, ""


def _collapse_spaced_letters(name: str) -> str:
    """Turn 'M I N T Y W O N G' / 'L I S A' into real words."""
    tokens = [t for t in re.split(r"\s+", (name or "").strip()) if t]
    if len(tokens) < 3:
        return name
    singles = sum(1 for t in tokens if len(t) == 1 and t.isalpha())
    if singles < max(3, int(len(tokens) * 0.65)):
        return name
    words: list[str] = []
    buf: list[str] = []
    for t in tokens:
        if len(t) == 1 and t.isalpha():
            buf.append(t)
        else:
            if buf:
                words.append("".join(buf))
                buf = []
            words.append(t)
    if buf:
        words.append("".join(buf))
    # Single glued token often includes surname: MINTYWONG → Minty Wong
    if len(words) == 1:
        given, sur = _split_embedded_surname(words[0])
        if sur:
            return f"{given} {sur}"
        return given
    return " ".join(words)


def _parse_followers(fields: list[str], blob: str) -> int:
    for f in fields:
        m = re.search(r"followers?\s*[:=]\s*([\d.,]+)\s*([kKmMbB])?", f)
        if m:
            n = float(m.group(1).replace(",", ""))
            suf = (m.group(2) or "").lower()
            if suf == "k":
                n *= 1_000
            elif suf == "m":
                n *= 1_000_000
            elif suf == "b":
                n *= 1_000_000_000
            return int(n)
    m = re.search(
        r"([\d.,]+)\s*([kKmM])?\s*Followers",
        blob or "",
        re.I,
    )
    if m:
        n = float(m.group(1).replace(",", ""))
        suf = (m.group(2) or "").lower()
        if suf == "k":
            n *= 1_000
        elif suf == "m":
            n *= 1_000_000
        return int(n)
    return 0


def _handle_name_tokens(handle: str) -> list[str]:
    """Mint tokens from @handle: mintywong_ → minty,wong; lisssssasum → lisa,lis,sum."""
    h = normalize_handle(handle).lower().strip("_")
    if not h:
        return []
    found: set[str] = set()
    parts = [p for p in re.split(r"[._\-+]+", h) if p]
    for part in parts:
        found.add(part)
        collapsed = re.sub(r"(.)\1{2,}", r"\1\1", part)
        found.add(collapsed)
        found.add(re.sub(r"(.)\1+", r"\1", part))
    blob = re.sub(r"[^a-z]", "", h)
    # Prefer longer given names first so "melissa" wins over "lisa"/"lis" when both match
    for name in sorted(_FEM_GIVEN | _MASC_GIVEN, key=len, reverse=True):
        min_len = 2 if name in {"yy", "yi", "ng", "su", "ka"} else 3
        if len(name) >= min_len and name in blob:
            found.add(name)
    for sur in _CJK_SURNAMES:
        if len(sur) >= 2 and sur in blob:
            found.add(sur)
    # Common HK handle patterns: ngcurtis, chanpinky, wongminty
    for sur in sorted(_CJK_SURNAMES, key=len, reverse=True):
        if len(sur) < 2:
            continue
        if blob.startswith(sur) and len(blob) > len(sur) + 2:
            found.add(blob[len(sur) :])
        if blob.endswith(sur) and len(blob) > len(sur) + 2:
            found.add(blob[: -len(sur)])
    return [t for t in found if t and len(t) >= 2]


def extract_profile_identity(
    scraped: str,
    scrape: Optional[dict[str, Any]] = None,
    handle: str = "",
) -> dict[str, Any]:
    """Pull structured identity crumbs: full name, first/last, bio, emojis, followers."""
    fields = list((scrape or {}).get("fields") or [])
    full_name = _field_value(fields, "full_name:", "json.full_name:", "ld+json.name:")
    if not full_name:
        m = re.search(r"full_name:([^\|]+)", scraped or "", re.I)
        if m:
            full_name = m.group(1).strip()
    if not full_name:
        og = _field_value(fields, "og:title:", "title:")
        m = re.match(r"^(.+?)\s*\(@", og or "")
        if m:
            full_name = m.group(1).strip()

    full_name = _collapse_spaced_letters(_strip_name_noise(full_name or ""))

    bio = _field_value(fields, "biography:", "json.biography:")
    if not bio:
        m = re.search(r"biography:([^\|]+)", scraped or "", re.I)
        if m:
            bio = m.group(1).strip()

    desc = _field_value(fields, "og:description:", "description:")
    desc_bio = ""
    if desc:
        m = re.search(r'on Instagram:\s*"([^"]+)"', desc, re.I | re.S)
        if m:
            desc_bio = m.group(1).strip()
        else:
            m = re.search(r'on Instagram:\s*[“"](.+?)[”"]', desc, re.I | re.S)
            if m:
                desc_bio = m.group(1).strip()
    # Merge: API biography is often truncated before "Just a girl…"
    bio_bits = [b for b in (bio, desc_bio) if b]
    if len(bio_bits) == 2 and bio_bits[0] not in bio_bits[1] and bio_bits[1] not in bio_bits[0]:
        bio = f"{bio_bits[0]} | {bio_bits[1]}"
    elif bio_bits:
        bio = max(bio_bits, key=len)

    parts = [p for p in re.split(r"\s+", full_name.strip()) if p] if full_name else []
    # Drop leftover single-letter crumbs after collapse failures
    alpha_parts = [p for p in parts if re.search(r"[A-Za-z]{2,}", p)]
    if alpha_parts:
        parts = alpha_parts
    first_name = parts[0] if parts else ""
    last_name = parts[-1] if len(parts) >= 2 else ""
    if len(parts) == 1:
        given, sur = _split_embedded_surname(parts[0])
        if sur:
            first_name, last_name = given, sur
    if len(parts) >= 2 and parts[0].lower() in _CJK_SURNAMES and parts[-1].lower() not in _CJK_SURNAMES:
        last_name, first_name = parts[0], parts[-1]
    elif len(parts) >= 2 and parts[-1].lower() in _CJK_SURNAMES:
        first_name, last_name = parts[0], parts[-1]

    handle_n = normalize_handle(handle)
    handle_tokens = _handle_name_tokens(handle_n)
    # If display name missing first, lift from handle (oh.my.vian → vian; ngcurtis → curtis)
    if not first_name or len(first_name) <= 1:
        for t in handle_tokens:
            tl = t.lower()
            if tl in _FEM_GIVEN or tl in _MASC_GIVEN:
                first_name = t.title() if t.islower() else t
                break
    if not last_name:
        for t in handle_tokens:
            if t.lower() in _CJK_SURNAMES:
                last_name = t.title()
                break

    pronouns = _field_value(fields, "pronouns:")
    city = _field_value(fields, "city:", "address:")
    category = _field_value(fields, "category:", "business_category:")
    blob_for_followers = "\n".join(fields) + "\n" + (scraped or "") + "\n" + (desc or "")
    followers = _parse_followers(fields, blob_for_followers)

    return {
        "handle": handle_n,
        "full_name": full_name,
        "first_name": first_name,
        "last_name": last_name,
        "handle_tokens": handle_tokens,
        "bio": bio,
        "description": desc or "",
        "pronouns": pronouns,
        "city": city,
        "category": category,
        "followers": followers,
        "emojis": list((scrape or {}).get("emojis") or []),
        "visibility": (scrape or {}).get("visibility") or "unknown",
        "web_text": ((scrape or {}).get("web_search") or {}).get("text") or "",
        "raw": scraped or "",
        "fields": fields,
    }


def _score_name_gender(
    first: str,
    last: str,
    full: str,
    handle_tokens: Optional[list[str]] = None,
) -> tuple[dict[str, float], list[str]]:
    scores = {"female": 0.0, "male": 0.0, "unknown": 0.0}
    ev: list[str] = []
    tokens = [t.lower() for t in re.findall(r"[A-Za-z]+", f"{first} {last} {full}")]
    for t in handle_tokens or []:
        if t.lower() not in tokens:
            tokens.append(t.lower())
    seen_f: set[str] = set()
    seen_m: set[str] = set()
    for t in tokens:
        if len(t) < 2:
            continue
        if t in _FEM_GIVEN and t not in seen_f:
            # Longer / clearer names weigh more (minty, vian, lisa, curtis)
            w = 4.5 if len(t) >= 4 else 3.5
            if t in {"lis", "yy", "sum", "mint"}:
                w = 3.0
            scores["female"] += w
            seen_f.add(t)
            ev.append(f"given/handle “{t}” → female")
        if t in _MASC_GIVEN and t not in seen_m:
            w = 4.5 if len(t) >= 4 else 3.5
            scores["male"] += w
            seen_m.add(t)
            ev.append(f"given/handle “{t}” → male")
    fl = (first or "").lower()
    if fl and fl.endswith(("ie", "y", "i")) and fl in _FEM_GIVEN:
        scores["female"] += 0.5
    # Western "First Last" with clear male given name (Curtis Ng)
    if fl in _MASC_GIVEN and (last or "").lower() in _CJK_SURNAMES:
        scores["male"] += 1.5
        ev.append(f"“{first} {last}” → male HK-style name")
    if fl in _FEM_GIVEN and (last or "").lower() in _CJK_SURNAMES:
        scores["female"] += 1.5
        ev.append(f"“{first} {last}” → female HK-style name")
    return scores, ev


def _score_bio_demographics(identity: dict[str, Any]) -> tuple[dict[str, Any], list[str]]:
    """Local text scores for gender / nationality / age from bio + name + handle."""
    bio = identity.get("bio") or ""
    full = identity.get("full_name") or ""
    handle = identity.get("handle") or ""
    web = identity.get("web_text") or ""
    pronouns = identity.get("pronouns") or ""
    city = identity.get("city") or ""
    category = identity.get("category") or ""
    desc = identity.get("description") or ""
    blob = (
        f"{bio}\n{desc}\n{full}\n{handle}\n{web}\n{pronouns}\n{city}\n{category}\n"
        + "\n".join(identity.get("fields") or [])
    )
    blob_l = blob.lower()
    ev: list[str] = []

    g_scores = {"female": 0.0, "male": 0.0, "unknown": 0.0}
    pr = pronouns.lower()
    if any(x in pr for x in ("she", "her", "她")):
        g_scores["female"] += 5
        ev.append("pronouns → female")
    if any(x in pr for x in ("he", "him", "他")) and "she" not in pr:
        g_scores["male"] += 5
        ev.append("pronouns → male")

    she = len(
        re.findall(
            r"\b(she|her|hers|女士|小姐|girl|girly|woman|female|wife|mum|mom|mama|mother|girlfriend|bride)\b",
            blob_l,
        )
    )
    he = len(
        re.findall(
            r"\b(he|him|his|先生|boy|man|male|husband|dad|papa|father|boyfriend|groom)\b",
            blob_l,
        )
    )
    # Soft pronouns in "Just a girl who…" are strong
    if re.search(r"\bjust a girl\b|\bi'?m a girl\b|\bas a girl\b|女孩|女生", blob_l):
        g_scores["female"] += 5
        ev.append("bio self-ID → girl/female")
    g_scores["female"] += she * 2.5
    g_scores["male"] += he * 2.5

    fem_emoji = ("👩", "♀️", "💃", "💅", "👗", "💄", "🎀", "👧", "👰", "👑", "💍")
    masc_emoji = ("👨", "♂️", "🧔", "💪", "👦", "🤵")
    g_scores["female"] += sum(blob.count(e) for e in fem_emoji) * 1.2
    g_scores["male"] += sum(blob.count(e) for e in masc_emoji) * 1.0
    # Wedding / couple stories: bride emoji beats boy/man noise
    if any(e in blob for e in ("👰", "💒")) and "🤵" not in blob:
        g_scores["female"] += 3.5
        g_scores["male"] = max(0.0, g_scores["male"] - 2.0)
        ev.append("bride/wedding emoji → female account")
    if she:
        ev.append("bio pronouns/words lean female")
    if he and g_scores["female"] <= g_scores["male"]:
        ev.append("bio pronouns/words lean male")

    name_g, name_ev = _score_name_gender(
        identity.get("first_name") or "",
        identity.get("last_name") or "",
        full,
        identity.get("handle_tokens") or [],
    )
    for k, v in name_g.items():
        g_scores[k] = g_scores.get(k, 0) + v
    ev.extend(name_ev)

    nat_scores: dict[str, float] = {}
    nat_rules: list[tuple[str, tuple[str, ...], float]] = [
        ("Hong Kong", ("hong kong", "hongkong", "hkig", "hker", "🇭🇰", "香港", "kowloon", "tsim sha", "hk ", "central", "mong kok", "causeway", "wan chai", "tst"), 4),
        ("Taiwan", ("taiwan", "taipei", "🇹🇼", "台灣", "台湾", "台北"), 4),
        ("China", ("beijing", "shanghai", "guangzhou", "shenzhen", "🇨🇳", "内地", "大陆"), 3),
        ("Japan", ("tokyo", "osaka", "japan", "🇯🇵", "日本", "東京"), 4),
        ("Korea", ("seoul", "korea", "🇰🇷", "한국", "首爾", "韩国"), 4),
        ("Singapore", ("singapore", "🇸🇬", "狮城", "sg "), 4),
        ("Malaysia", ("malaysia", "kuala lumpur", "🇲🇾"), 3),
        ("United Kingdom", ("london", "britain", "british", "🇬🇧", "england", "uk "), 3),
        ("United States", ("usa", "united states", "new york", "los angeles", "🇺🇸", "nyc"), 3),
        ("Australia", ("sydney", "melbourne", "australia", "🇦🇺"), 3),
        ("Canada", ("toronto", "vancouver", "canada", "🇨🇦"), 3),
        ("France", ("paris", "france", "🇫🇷"), 3),
        ("Philippines", ("manila", "philippines", "🇵🇭", "pinoy"), 3),
        ("India", ("mumbai", "delhi", "india", "🇮🇳"), 3),
    ]
    for label, keys, weight in nat_rules:
        hits = sum(1 for k in keys if k in blob_l)
        if hits:
            nat_scores[label] = nat_scores.get(label, 0) + hits * weight
            ev.append(f"bio/locale/web “{label}”")

    city_l = city.lower()
    if city_l:
        for label, keys, weight in nat_rules:
            if any(k.strip() in city_l for k in keys if len(k.strip()) > 2):
                nat_scores[label] = nat_scores.get(label, 0) + weight + 2
                ev.append(f"profile city → {label}")
                break
        if any(x in city_l for x in ("hong kong", "hk", "kowloon", "香港")):
            nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 6
            ev.append("city → Hong Kong")

    last = (identity.get("last_name") or "").lower()
    first = (identity.get("first_name") or "").lower()
    handle_toks = [t.lower() for t in (identity.get("handle_tokens") or [])]
    if last in _CJK_SURNAMES or first in _CJK_SURNAMES or any(t in _CJK_SURNAMES for t in handle_toks):
        nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 2.5
        sur = last or first or next((t for t in handle_toks if t in _CJK_SURNAMES), "")
        ev.append(f"surname “{sur}” → Chinese / HK-leaning")

    cjk_chars = len(re.findall(r"[\u4e00-\u9fff]", blob))
    if cjk_chars >= 2:
        if "香港" in blob:
            nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 5
        elif any(ch in blob for ch in "國語灣臺體"):
            nat_scores["Taiwan"] = nat_scores.get("Taiwan", 0) + 3
        else:
            nat_scores["Chinese-speaking"] = nat_scores.get("Chinese-speaking", 0) + 1.5

    followers = int(identity.get("followers") or 0)
    foodie = any(
        k in blob_l
        for k in (
            "food", "foodie", "eat", "dining", "restaurant", "sushi", "wine",
            "美食", "食", "dine", "cafe", "café", "brunch",
        )
    )
    if followers >= 8_000 and foodie:
        nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 1.5
        ev.append(f"public foodie KOL (~{followers:,} followers)")

    age_guess = "unknown"
    age_m = re.search(r"(?:age|歲|岁|y/?o|years?\s*old)[^\d]{0,6}(\d{2})", blob_l)
    age_m2 = re.search(r"\b(1[6-9]|2[0-9]|3[0-9]|4[0-9]|5[0-9])\s*(?:y/?o|歲|岁)\b", blob_l)
    age_num = int(age_m.group(1)) if age_m else (int(age_m2.group(1)) if age_m2 else None)
    if age_num and 16 <= age_num <= 70:
        age_guess = _age_band(age_num)
        ev.append(f"stated age ~{age_num}")
    elif any(k in blob_l for k in ("uni", "university", "college", "polyu", "hku", "cuhk", "學生", "大学", "大學", "freshman")):
        age_guess = "early 20s"
        ev.append("student life-stage")
    elif any(k in blob_l for k in ("mba", "wedding", "married", "老公", "老婆", "結婚", "bride")):
        age_guess = "late 20s–30s"
        ev.append("adult life-stage")
    elif any(k in blob_l for k in ("mum", "mom", "mama", "dad", "papa", "kids", "son", "daughter", "媽媽", "爸爸")):
        age_guess = "30s–40s"
        ev.append("parent life-stage")
    elif any(k in blob_l for k in ("gen z", "genz", "tiktok", "xiaohongshu", "小红书", "小紅書")):
        age_guess = "early–mid 20s"
        ev.append("gen-Z platform cues")
    elif any(k in blob_l for k in ("retired", "grandkids", "grandchild", "退休")):
        age_guess = "50+"
        ev.append("senior life-stage")
    elif followers >= 5_000 and foodie:
        age_guess = "late 20s–30s"
        ev.append("KOL foodie → likely under 40")
    elif followers >= 5_000 and age_guess == "unknown":
        age_guess = "20s–30s"
        ev.append("public creator → likely under 40")

    return {
        "gender_scores": g_scores,
        "nat_scores": nat_scores,
        "age_guess": age_guess,
    }, ev


def _age_band(age: int) -> str:
    if age < 20:
        return "late teens"
    if age < 25:
        return "early 20s"
    if age < 30:
        return "late 20s"
    if age < 35:
        return "early 30s"
    if age < 40:
        return "late 30s"
    if age < 50:
        return "40s"
    return "50+"


def _facepp_credentials() -> tuple[str, str]:
    try:
        from dotenv import load_dotenv

        load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"), override=True)
    except ImportError:
        pass
    key = (os.environ.get("FACEPP_API_KEY") or FACEPP_API_KEY or "").strip()
    secret = (os.environ.get("FACEPP_API_SECRET") or FACEPP_API_SECRET or "").strip()
    try:
        key = key or str(st.secrets.get("FACEPP_API_KEY", "") or "").strip()
        secret = secret or str(st.secrets.get("FACEPP_API_SECRET", "") or "").strip()
    except Exception:
        pass
    return key, secret


def _ethnicity_to_locale(ethnicity: str) -> tuple[str, list[str]]:
    """Map Face++ ethnicity → region_guess + nationality_hints for this club."""
    e = (ethnicity or "").strip().upper()
    if e in {"ASIAN", "ASIAN_EAST", "EAST_ASIAN"}:
        return "East Asian", ["Hong Kong", "China", "Taiwan"]
    if e in {"INDIA", "INDIAN", "SOUTH_ASIAN"}:
        return "South Asian", ["India"]
    if e in {"WHITE", "CAUCASIAN"}:
        return "White/European", []
    if e in {"BLACK", "AFRICAN"}:
        return "Black/African", []
    if e in {"MIDDLE_EASTERN", "ARAB"}:
        return "Middle Eastern", []
    if e in {"LATINO", "HISPANIC"}:
        return "Latino", []
    return "unknown", []


def analyze_face_facepp(photo_path: str) -> dict[str, Any]:
    """
    Face++ Detect API — gender, age, ethnicity (nationality cue).
    Docs: https://console.faceplusplus.com/documents/7078057
    """
    key, secret = _facepp_credentials()
    if not key or key.startswith("your_"):
        return {"ok": False, "note": "FACEPP_API_KEY missing in .env"}
    if not secret or secret.startswith("your_"):
        return {
            "ok": False,
            "note": "FACEPP_API_SECRET missing — Face++ needs both API Key and API Secret from console.faceplusplus.com",
        }

    full = resolve_media_path(photo_path) if not os.path.isabs(photo_path) else photo_path
    if not full or not os.path.isfile(full):
        return {"ok": False, "note": "no photo file for Face++"}

    base = (os.environ.get("FACEPP_API_BASE") or FACEPP_API_BASE).rstrip("/")
    url = f"{base}/detect"
    try:
        with open(full, "rb") as f:
            raw = f.read()
        # Prefer smaller JPEG for upload quotas
        try:
            from io import BytesIO
            from PIL import Image

            im = Image.open(BytesIO(raw)).convert("RGB")
            w, h = im.size
            scale = min(1.0, 900.0 / float(max(w, h)))
            if scale < 1.0:
                im = im.resize((max(1, int(w * scale)), max(1, int(h * scale))), Image.Resampling.LANCZOS)
            buf = BytesIO()
            im.save(buf, format="JPEG", quality=88, optimize=True)
            raw = buf.getvalue()
        except Exception:
            pass

        files = {"image_file": (os.path.basename(full) or "face.jpg", raw, "image/jpeg")}
        data = {
            "api_key": key,
            "api_secret": secret,
            "return_attributes": "gender,age,ethnicity,smiling,emotion",
        }
        resp = requests.post(url, data=data, files=files, timeout=45)
    except OSError as exc:
        return {"ok": False, "note": f"read photo failed: {exc}"}
    except requests.RequestException as exc:
        return {"ok": False, "note": f"Face++ request failed: {type(exc).__name__}"}

    try:
        payload = resp.json()
    except Exception:
        return {"ok": False, "note": f"Face++ bad JSON HTTP {resp.status_code}"}

    if resp.status_code != 200 or payload.get("error_message"):
        err = payload.get("error_message") or payload.get("error") or f"HTTP {resp.status_code}"
        return {"ok": False, "note": f"Face++: {err}"}

    faces = payload.get("faces") or []
    if not faces:
        return {"ok": False, "note": "Face++: no face detected"}

    # Largest face by rectangle area
    def _area(face: dict) -> int:
        rect = face.get("face_rectangle") or {}
        try:
            return int(rect.get("width") or 0) * int(rect.get("height") or 0)
        except (TypeError, ValueError):
            return 0

    face = max(faces, key=_area) if isinstance(faces[0], dict) else {}
    attrs = face.get("attributes") or {}

    gender_raw = str((attrs.get("gender") or {}).get("value") or "").strip().lower()
    gender = "unknown"
    if gender_raw in ("female", "f"):
        gender = "female"
    elif gender_raw in ("male", "m"):
        gender = "male"

    age_val = 0
    try:
        age_val = int((attrs.get("age") or {}).get("value") or 0)
    except (TypeError, ValueError):
        age_val = 0
    age_band = _age_band(age_val) if age_val else "unknown"
    age_low = max(16, age_val - 3) if age_val else 0
    age_high = min(80, age_val + 3) if age_val else 0

    ethnicity = str((attrs.get("ethnicity") or {}).get("value") or "").strip()
    region, nat_hints = _ethnicity_to_locale(ethnicity)
    # Club prior: Asian face + HK tennis club → Hong Kong as top hint
    if region == "East Asian" and "Hong Kong" not in nat_hints:
        nat_hints = ["Hong Kong"] + list(nat_hints)

    smile = 0.0
    try:
        smile = float((attrs.get("smiling") or {}).get("value") or 0)
    except (TypeError, ValueError):
        smile = 0.0
    emotion = ""
    emotions = attrs.get("emotion") or {}
    if isinstance(emotions, dict) and emotions:
        def _emo_value(node: Any) -> float:
            if isinstance(node, dict):
                try:
                    return float(node.get("value") or 0)
                except (TypeError, ValueError):
                    return 0.0
            try:
                return float(node or 0)
            except (TypeError, ValueError):
                return 0.0

        emotion = max(emotions, key=_emo_value)

    conf = 0.78 if gender in ("female", "male") else 0.4
    if gender in ("female", "male") and age_val:
        conf = 0.88

    return {
        "ok": gender in ("female", "male") or age_band != "unknown",
        "gender": gender,
        "age_band": age_band,
        "age_low": age_low,
        "age_high": age_high,
        "region_guess": region,
        "nationality_hints": nat_hints[:3],
        "ethnicity": ethnicity,
        "smile": smile,
        "emotion": emotion,
        "person_visible": True,
        "photos_used": 1,
        "photos_analyzed": 1,
        "confidence": conf,
        "cues": (
            f"Face++: {gender_raw or gender}, age~{age_val}"
            + (f", ethnicity {ethnicity}" if ethnicity else "")
        ),
        "model": "faceplusplus-detect",
        "note": f"vision via Face++ ({gender}, {age_band}, {ethnicity or 'eth?'})",
    }


def analyze_ig_photos(photo_paths: list[str]) -> dict[str, Any]:
    """
    Primary vision: Face++ Detect on profile + feed photos (vote).
    NewCoin deepseek-v3.2 is text-only — do not call it for images.
    """
    paths = [p for p in photo_paths if p and os.path.isfile(p)]
    if not paths:
        resolved = []
        for p in photo_paths:
            full = resolve_media_path(p) if p else ""
            if full:
                resolved.append(full)
        paths = resolved
    if not paths:
        return {"ok": False, "note": "no photos on disk for vision"}

    votes: list[dict[str, Any]] = []
    errors: list[str] = []
    for p in paths[:VISION_MAX_IMAGES]:
        one = analyze_face_facepp(p)
        if one.get("ok"):
            votes.append(one)
        else:
            errors.append(str(one.get("note") or "fail"))

    if votes:
        agg = _aggregate_vision_votes(votes)
        # Prefer ethnicity/nationality hints from Face++ votes
        hints: list[str] = []
        eth_counts: dict[str, int] = {}
        for v in votes:
            for h in v.get("nationality_hints") or []:
                if h:
                    hints.append(str(h))
            eth = str(v.get("ethnicity") or "").strip()
            if eth:
                eth_counts[eth] = eth_counts.get(eth, 0) + 1
            region = str(v.get("region_guess") or "")
            if region and region != "unknown":
                agg["region_guess"] = region
        if hints:
            agg["nationality_hints"] = list(dict.fromkeys(hints))[:3]
        if eth_counts:
            top_eth = max(eth_counts.items(), key=lambda x: x[1])[0]
            agg["ethnicity"] = top_eth
        if agg.get("ok"):
            agg["note"] = f"Face++ vote across {len(votes)} photo(s)"
            agg["model"] = "faceplusplus-detect"
            return agg
        errors.append(agg.get("note") or "vote weak")

    return {
        "ok": False,
        "note": "; ".join(dict.fromkeys(errors))[:300] or "face analysis failed",
        "photos_analyzed": len(paths),
    }


def analyze_profile_photo(photo_path: str) -> dict[str, Any]:
    """Back-compat: single profile photo vision via Face++."""
    full = resolve_media_path(photo_path) if photo_path else ""
    if not full:
        return {"ok": False, "note": "no profile photo on disk"}
    return analyze_ig_photos([full])


def _aggregate_vision_votes(results: list[dict[str, Any]]) -> dict[str, Any]:
    """Majority / confidence-weighted vote across per-image vision calls."""
    if not results:
        return {"ok": False, "note": "no vision votes"}
    g_w = {"female": 0.0, "male": 0.0}
    age_w: dict[str, float] = {}
    region_w: dict[str, float] = {}
    hints: list[str] = []
    cues: list[str] = []
    models: list[str] = []
    age_low_vals: list[int] = []
    age_high_vals: list[int] = []
    for r in results:
        conf = float(r.get("confidence") or 0.55)
        conf = max(0.2, min(conf, 1.0))
        g = str(r.get("gender") or "unknown").lower()
        if g in g_w:
            g_w[g] += conf
        age = str(r.get("age_band") or "unknown")
        if age and age != "unknown":
            age_w[age] = age_w.get(age, 0) + conf
        region = str(r.get("region_guess") or "unknown")
        if region and region != "unknown":
            region_w[region] = region_w.get(region, 0) + conf
        for h in r.get("nationality_hints") or []:
            if h:
                hints.append(str(h))
        if r.get("cues"):
            cues.append(str(r.get("cues")))
        if r.get("model"):
            models.append(str(r["model"]))
        try:
            if int(r.get("age_low") or 0):
                age_low_vals.append(int(r["age_low"]))
            if int(r.get("age_high") or 0):
                age_high_vals.append(int(r["age_high"]))
        except (TypeError, ValueError):
            pass
    gender = "unknown"
    if g_w["female"] >= g_w["male"] + 0.15:
        gender = "female"
    elif g_w["male"] >= g_w["female"] + 0.15:
        gender = "male"
    elif max(g_w.values()) > 0:
        gender = "female" if g_w["female"] >= g_w["male"] else "male"
    age_band = max(age_w.items(), key=lambda x: x[1])[0] if age_w else "unknown"
    region = max(region_w.items(), key=lambda x: x[1])[0] if region_w else "unknown"
    total = g_w["female"] + g_w["male"]
    conf = 0.0
    if total > 0 and gender in g_w:
        conf = min(0.95, 0.45 + (g_w[gender] / total) * 0.5 + min(len(results), 4) * 0.05)
    uniq_hints = list(dict.fromkeys(hints))[:3]
    return {
        "ok": gender != "unknown" or age_band != "unknown" or bool(uniq_hints),
        "gender": gender,
        "age_band": age_band,
        "age_low": min(age_low_vals) if age_low_vals else 0,
        "age_high": max(age_high_vals) if age_high_vals else 0,
        "region_guess": region,
        "nationality_hints": uniq_hints,
        "person_visible": gender != "unknown",
        "photos_used": len(results),
        "photos_analyzed": len(results),
        "confidence": conf,
        "cues": " | ".join(dict.fromkeys(cues))[:280],
        "model": models[0] if models else "",
        "note": f"vision vote across {len(results)} photo(s)",
    }


def _parse_json_object(raw: str) -> Optional[dict[str, Any]]:
    text = (raw or "").strip()
    text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.I).strip()
    try:
        data = json.loads(text)
        return data if isinstance(data, dict) else None
    except Exception:
        m = re.search(r"\{.*\}", text, re.S)
        if not m:
            return None
        try:
            data = json.loads(m.group(0))
            return data if isinstance(data, dict) else None
        except Exception:
            return None


def _llm_text_demographics(
    identity: dict[str, Any],
    local: dict[str, Any],
    local_evidence: list[str],
) -> Optional[dict[str, Any]]:
    """
    Strong text-only pass — used even when vision fails.
    Explicit HK nickname / handle / bio rules so we don't leave gender blank.
    """
    client = get_client()
    if client is None:
        return None
    payload = {
        "handle": identity.get("handle"),
        "full_name": identity.get("full_name"),
        "first_name": identity.get("first_name"),
        "last_name": identity.get("last_name"),
        "handle_tokens": identity.get("handle_tokens"),
        "bio": identity.get("bio"),
        "description": (identity.get("description") or "")[:500],
        "pronouns": identity.get("pronouns"),
        "city": identity.get("city"),
        "category": identity.get("category"),
        "followers": identity.get("followers"),
        "emojis": identity.get("emojis"),
        "visibility": identity.get("visibility"),
        "web_crumbs": (identity.get("web_text") or "")[:500],
        "local_scores": local,
        "local_evidence": local_evidence[:14],
    }
    prompt = (
        "Estimate Instagram demographics for a HK tennis club signup. "
        "Be decisive when signals are clear — avoid 'unknown' gender if a clear name or bio self-ID exists.\n"
        "Rules:\n"
        "- Female nicknames/handles: Minty, Vian, Vivian, Lisa, Lissa, Lis, Phoebe, Pinky, Queenie, "
        "Amy, Angela, Shannon, Manyee, Summer, YY, Suet Yi → female\n"
        "- Male names: Curtis, Kevin, Ken, David, Jason, Michael, Andrew → male\n"
        "- Romanized Chinese surnames Wong/Chan/Ng/Chow/Lam/Leung + English given name → often Hong Kong\n"
        "- Bio with girl/she/her/女士/小姐/👰 → female; he/him/先生/🤵 alone → male\n"
        "- Public foodie KOL (5k+ followers, dining/sushi/wine) in HK style → female often, age under 40, "
        "nationality Hong Kong when surname/locale cues exist\n"
        "- Spaced letter names like M I N T Y mean Minty\n"
        "Return ONLY JSON:\n"
        '{"gender":"female|male|unknown","nationality":"string","age_guess":"age band",'
        '"confidence":0.0,"rationale":"one short sentence"}'
    )
    try:
        completion = client.chat.completions.create(
            model=active_model(),
            messages=[
                {"role": "system", "content": prompt},
                {"role": "user", "content": json.dumps(payload, ensure_ascii=False)},
            ],
            temperature=0.05,
            max_tokens=DEMO_MAX_TOKENS,
        )
        return _parse_json_object(completion_text(completion))
    except Exception:
        return None


def _llm_fuse_demographics(
    identity: dict[str, Any],
    photo: dict[str, Any],
    local: dict[str, Any],
    local_evidence: list[str],
) -> Optional[dict[str, Any]]:
    """Ask the text model to reconcile photo + name + bio into one guess."""
    client = get_client()
    if client is None:
        return None
    payload = {
        "identity": {
            "handle": identity.get("handle"),
            "full_name": identity.get("full_name"),
            "first_name": identity.get("first_name"),
            "last_name": identity.get("last_name"),
            "handle_tokens": identity.get("handle_tokens"),
            "bio": identity.get("bio"),
            "followers": identity.get("followers"),
            "pronouns": identity.get("pronouns"),
            "city": identity.get("city"),
            "category": identity.get("category"),
            "emojis": identity.get("emojis"),
            "visibility": identity.get("visibility"),
            "web_crumbs": (identity.get("web_text") or "")[:600],
        },
        "photo_analysis": {k: photo.get(k) for k in (
            "ok", "gender", "age_band", "age_low", "age_high", "region_guess",
            "nationality_hints", "confidence", "cues", "note",
            "photos_used", "photos_analyzed", "person_visible",
        )},
        "local_heuristic": local,
        "local_evidence": local_evidence[:12],
    }
    prompt = (
        "You reconcile demographics for a tennis club signup. "
        "VISION (profile + public feed photos) is the PRIMARY signal for gender and age when ok=true "
        "and confidence>=0.45 — do not override clear vision gender with unknown. "
        "Use name/handle/bio to reinforce or fill nationality and gaps only. "
        "Clear names (Minty/Vian/Lisa/Curtis) still matter if vision failed. "
        "Return ONLY JSON:\n"
        '{"gender":"female|male|unknown","nationality":"string","age_guess":"age band",'
        '"confidence":0.0,"rationale":"one short sentence","sources":["vision","name","bio"]}'
    )
    try:
        completion = client.chat.completions.create(
            model=active_model(),
            messages=[
                {"role": "system", "content": prompt},
                {"role": "user", "content": json.dumps(payload, ensure_ascii=False)},
            ],
            temperature=0.1,
            max_tokens=DEMO_MAX_TOKENS,
        )
        return _parse_json_object(completion_text(completion))
    except Exception:
        return None


def _pick_gender(scores: dict[str, float]) -> str:
    female = scores.get("female", 0)
    male = scores.get("male", 0)
    if female <= 0 and male <= 0:
        return "unknown"
    # Clear majority
    if female >= male + 0.75:
        return "female"
    if male >= female + 0.75:
        return "male"
    # Tie-ish but both non-trivial → unknown only if truly tied
    if abs(female - male) < 0.5 and max(female, male) >= 3:
        return "unknown"
    return "female" if female > male else "male"


def _pick_nationality(nat_scores: dict[str, float], photo: dict[str, Any]) -> str:
    hints = photo.get("nationality_hints") if isinstance(photo.get("nationality_hints"), list) else []
    region = str(photo.get("region_guess") or "")
    merged = dict(nat_scores)
    for h in hints:
        label = str(h).strip()
        if not label:
            continue
        low = label.lower()
        if "hong kong" in low or low in {"hk", "hkg"}:
            label = "Hong Kong"
        merged[label] = merged.get(label, 0) + 2.0
    if region and "East Asian" in region:
        if not any(k in merged for k in ("Hong Kong", "Taiwan", "China", "Japan", "Korea", "Singapore")):
            merged["Hong Kong"] = merged.get("Hong Kong", 0) + 1.2
        else:
            merged["Hong Kong"] = merged.get("Hong Kong", 0) + 0.4
    if not merged:
        return "unknown"
    return max(merged.items(), key=lambda x: x[1])[0]


def _apply_llm_demo(
    gender: str,
    nationality: str,
    age_guess: str,
    llm: Optional[dict[str, Any]],
    g_scores: dict[str, float],
    evidence: list[str],
    tag: str,
    *,
    vision_gender: str = "",
    vision_conf: float = 0.0,
) -> tuple[str, str, str]:
    """Merge an LLM guess without wiping strong vision or name/bio signals."""
    if not llm:
        return gender, nationality, age_guess
    strong_local = max(g_scores.get("female", 0), g_scores.get("male", 0)) >= 3.0
    local_gender = _pick_gender(g_scores)
    strong_vision = vision_gender in ("female", "male") and vision_conf >= 0.45
    fg = str(llm.get("gender") or "").lower()
    if fg in ("female", "male"):
        if strong_vision and fg != vision_gender:
            evidence.append(f"{tag}: kept vision {vision_gender} over LLM {fg}")
        elif strong_local and local_gender in ("female", "male") and fg != local_gender and not strong_vision:
            evidence.append(f"{tag}: kept local {local_gender} over LLM {fg}")
        else:
            gender = fg
    elif fg == "unknown" and gender in ("female", "male"):
        evidence.append(f"{tag}: ignored LLM unknown (kept {gender})")
    fn = str(llm.get("nationality") or "").strip()
    if fn and fn.lower() != "unknown":
        if nationality.lower() == "unknown" or float(llm.get("confidence") or 0) >= 0.45:
            nationality = fn
    fa = str(llm.get("age_guess") or "").strip()
    if fa and fa.lower() != "unknown":
        if age_guess.lower() == "unknown" or float(llm.get("confidence") or 0) >= 0.45:
            # Vision age wins when confident
            if not (strong_vision and age_guess != "unknown" and vision_conf >= 0.55):
                age_guess = fa
    if llm.get("rationale"):
        evidence.append(f"{tag}: {llm.get('rationale')}")
    return gender, nationality, age_guess


def _disk_named_photos(folder: str, handle: str) -> list[str]:
    handle = normalize_handle(handle)
    if not handle or not os.path.isdir(folder):
        return []
    found: list[str] = []
    for name in sorted(os.listdir(folder)):
        if name.startswith(f"{handle}_"):
            full = os.path.join(folder, name)
            if os.path.isfile(full):
                found.append(full)
    return found


def _person_match_blob(votes: list[dict[str, Any]]) -> str:
    """Light keywords from person photos so the animal match can see the same frames as the gate."""
    bits: list[str] = []
    for vote in votes:
        source = vote.get("source") or "photo"
        bits.append("profile photo" if source == "profile" else "feed photo person")
        smile = 0.0
        try:
            smile = float(vote.get("smile") or 0)
        except (TypeError, ValueError):
            smile = 0.0
        if vote.get("emotion") == "happiness" or smile >= 45:
            bits.append("chill smile")
    return " ".join(bits)


def gather_person_vision(
    handle: str,
    profile_rel: str = "",
    feed_rels: Optional[list[str]] = None,
    pin_rels: Optional[list[str]] = None,
    *,
    include_saved: bool = True,
) -> dict[str, Any]:
    """
    Gate + animal inputs: the profile photo, plus pinned/feed frames that contain a person.
    Food, logos, and scenery are skipped.
    """
    items: list[tuple[str, str]] = []
    seen: set[str] = set()

    def _add(kind: str, rel: str) -> None:
        if not rel:
            return
        full = rel if os.path.isabs(rel) else (resolve_media_path(rel) or "")
        if not full or not os.path.isfile(full) or full in seen:
            return
        seen.add(full)
        items.append((kind, full))

    _add("profile", profile_rel)
    if include_saved:
        for rel in _disk_named_photos(os.path.join(PROFILE_DIR, "pins"), handle):
            _add("pin", rel)
    for rel in pin_rels or []:
        _add("pin", rel)
    for rel in feed_rels or []:
        _add("feed", rel)
    if include_saved:
        for rel in _disk_named_photos(os.path.join(PROFILE_DIR, "feed"), handle):
            _add("feed", rel)

    votes: list[dict[str, Any]] = []
    used: list[str] = []
    person_extra = 0
    for kind, full in items[:7]:
        one = analyze_face_facepp(full)
        person = bool(one.get("ok") and one.get("person_visible"))
        if not person:
            continue
        one = dict(one)
        one["source"] = kind
        votes.append(one)
        used.append(full)
        if kind != "profile":
            person_extra += 1

    if not votes:
        return {
            "ok": False,
            "note": "no person in profile or feed photos",
            "person_paths": [],
            "person_feed_count": 0,
            "photos_analyzed": len(items),
            "match_blob": "",
        }
    agg = _aggregate_vision_votes(votes)
    agg["person_paths"] = used
    agg["person_feed_count"] = person_extra
    agg["photos_analyzed"] = len(items)
    agg["match_blob"] = _person_match_blob(votes)
    agg["note"] = (
        f"Face++ on profile + {person_extra} person photo(s) from pins/feed"
        if any(v.get("source") == "profile" for v in votes)
        else f"Face++ on {person_extra} person photo(s) from pins/feed"
    )
    return agg


def infer_demographics(
    scraped: str,
    scrape: Optional[dict[str, Any]] = None,
    handle: str = "",
    ig_photo_path: str = "",
) -> dict[str, str]:
    """
    Ordered pipeline:
      1) Web / DeepSeek research (KOL, gender, locale) — before trusting IG alone
      2) Public IG → HD profile + up to 3 feed photos → vision
         Private IG → name + low-res profile pic → vision/name
      3) Name/bio heuristics + text fusion for gaps
    """
    scrape = scrape or {}
    identity = extract_profile_identity(scraped, scrape=scrape, handle=handle)
    local, local_ev = _score_bio_demographics(identity)

    g_scores = dict(local.get("gender_scores") or {})
    nat_scores = dict(local.get("nat_scores") or {})
    age_guess = str(local.get("age_guess") or "unknown")
    evidence = list(local_ev)
    steps: list[str] = []

    # --- Step 1: web / DeepSeek research (KOL) ---
    research = scrape.get("web_research") if isinstance(scrape.get("web_research"), dict) else None
    if not research and handle:
        research = research_handle_before_ig(handle)
        scrape["web_research"] = research
    research = research or {}
    is_kol = bool(research.get("is_kol"))
    followers = int(identity.get("followers") or 0)
    if followers >= KOL_FOLLOWER_MIN:
        is_kol = True
        evidence.append(f"followers {followers:,} → KOL-scale")
    if is_kol:
        evidence.append(
            f"KOL detected ({research.get('kol_niche') or 'creator'})"
        )
        steps.append("1_web_kol")
        # HK foodie KOL prior
        niche = str(research.get("kol_niche") or "").lower()
        if niche in ("foodie", "lifestyle", "beauty", "fashion") or "food" in niche:
            nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 2.0
            if age_guess == "unknown":
                age_guess = "late 20s–30s"
                evidence.append("KOL foodie/lifestyle → under 40 prior")
    rg = str(research.get("gender") or "").lower()
    if rg in ("female", "male"):
        conf_w = 3.5 + float(research.get("confidence") or 0.4) * 3.0
        if is_kol:
            conf_w += 2.0
        g_scores[rg] = g_scores.get(rg, 0) + conf_w
        evidence.append(f"step1 web/DeepSeek → {rg} (KOL={is_kol})")
        steps.append("1_web_gender")
    rn = str(research.get("nationality") or "").strip()
    if rn and rn.lower() not in ("unknown", "other", ""):
        nat_scores[rn] = nat_scores.get(rn, 0) + 3.5 + (1.5 if is_kol else 0)
        evidence.append(f"step1 web nationality → {rn}")
    ra = str(research.get("age_guess") or "").strip()
    if ra and ra.lower() != "unknown" and age_guess == "unknown":
        age_guess = ra
        evidence.append(f"step1 web age → {ra}")
    if research.get("rationale"):
        evidence.append(f"step1: {research.get('rationale')}")

    # --- Step 2: vision (public HD+feed vs private low-res) ---
    visibility = str(scrape.get("visibility") or "unknown").lower()
    profile_rel = ig_photo_path or scrape.get("ig_photo_path") or ""
    feed_rels = list(scrape.get("ig_feed_paths") or [])
    profile_meta = scrape.get("profile_photo_meta") or (
        _image_file_meta(profile_rel) if profile_rel else {}
    )
    feed_meta = list(scrape.get("feed_photo_meta") or [])

    if visibility == "private":
        steps.append("2_private_name_lowres")
        feed_rels = []
        pin_rels = []
        evidence.append("private IG → name + profile pic only")
    else:
        steps.append("2_public_pins_hd")
        pin_rels = list(scrape.get("ig_pinned_paths") or [])
        if handle and not feed_rels:
            feed_rels = download_ig_feed_photos(handle, max_photos=FEED_PHOTO_MAX)
            scrape["ig_feed_paths"] = feed_rels
            feed_meta = [_image_file_meta(p) for p in feed_rels]
            scrape["feed_photo_meta"] = feed_meta
        if profile_meta.get("full_res") or profile_meta.get("hd"):
            evidence.append(
                f"profile photo {profile_meta.get('width')}x{profile_meta.get('height')} "
                f"({profile_meta.get('bytes', 0)} bytes"
                f"{', full-res' if profile_meta.get('full_res') else ', HD'})"
            )
        else:
            evidence.append(
                f"profile photo {profile_meta.get('width', 0)}x{profile_meta.get('height', 0)} "
                f"({profile_meta.get('bytes', 0)} bytes)"
            )
        evidence.append(f"pinned photos on disk: {len(pin_rels)}/{PINNED_PHOTO_MAX}")
        evidence.append(f"feed photos on disk: {len(feed_rels)}/{FEED_PHOTO_MAX}")

    photo = gather_person_vision(
        handle,
        profile_rel,
        [] if visibility == "private" else feed_rels,
        [] if visibility == "private" else pin_rels,
        include_saved=visibility != "private",
    )
    scrape["vision"] = photo
    if visibility != "private":
        evidence.append(
            f"person photos used: profile + {photo.get('person_feed_count') or 0} feed/pin "
            f"(skipped frames with no face)"
        )

    vision_gender = ""
    vision_conf = 0.0
    if photo.get("ok"):
        vision_conf = float(photo.get("confidence") or 0.55)
        weight = 6.0 + max(0.0, min(vision_conf, 1.0)) * 8.0
        n_photos = int(photo.get("photos_used") or len(photo.get("person_paths") or []) or 0)
        if n_photos >= 2 and visibility != "private":
            weight += 2.5
        pg = str(photo.get("gender") or "unknown").lower()
        if pg in ("female", "male"):
            vision_gender = pg
            g_scores[pg] = g_scores.get(pg, 0) + weight
            evidence.append(
                f"step2 VISION → {pg} (conf {vision_conf:.2f}, {n_photos} photo(s), {visibility})"
            )
            steps.append("2_vision_ok")
        p_age = str(photo.get("age_band") or "unknown")
        if p_age and p_age != "unknown":
            age_guess = p_age
            evidence.append(f"step2 VISION age → {p_age}")
        region = photo.get("region_guess")
        if region and region != "unknown":
            evidence.append(f"step2 VISION region → {region}")
            if "East Asian" in str(region):
                nat_scores["Hong Kong"] = nat_scores.get("Hong Kong", 0) + 1.5
        for h in photo.get("nationality_hints") or []:
            if h:
                evidence.append(f"step2 VISION hint → {h}")
        if photo.get("note"):
            evidence.append(str(photo.get("note")))
    else:
        evidence.append(f"step2 vision unavailable: {photo.get('note') or 'failed'}")
        steps.append("2_vision_fail")

    # --- Step 3: fuse ---
    steps.append("3_fuse")
    gender = _pick_gender(g_scores)
    if vision_gender and vision_conf >= 0.45:
        gender = vision_gender
    nationality = _pick_nationality(nat_scores, photo if photo.get("ok") else {})

    text_llm = _llm_text_demographics(identity, local, evidence)
    gender, nationality, age_guess = _apply_llm_demo(
        gender,
        nationality,
        age_guess,
        text_llm,
        g_scores,
        evidence,
        "text-llm",
        vision_gender=vision_gender,
        vision_conf=vision_conf,
    )

    fused = _llm_fuse_demographics(identity, photo, local, evidence)
    gender, nationality, age_guess = _apply_llm_demo(
        gender,
        nationality,
        age_guess,
        fused,
        g_scores,
        evidence,
        "fusion",
        vision_gender=vision_gender,
        vision_conf=vision_conf,
    )
    sources = (fused or {}).get("sources") if fused else None
    if isinstance(sources, list) and sources:
        evidence.append("sources: " + ", ".join(str(s) for s in sources))

    if vision_gender and vision_conf >= 0.45:
        gender = vision_gender
    elif gender == "unknown":
        forced = _pick_gender(g_scores)
        if forced in ("female", "male") and max(g_scores.get("female", 0), g_scores.get("male", 0)) >= 3:
            gender = forced
            evidence.append(f"fallback name/handle → {gender}")

    # KOL + clear female web research should not stay unknown
    if gender == "unknown" and is_kol and rg in ("female", "male"):
        gender = rg
        evidence.append(f"KOL web gender lock → {gender}")

    name_bit = identity.get("full_name") or ""
    if identity.get("first_name") or identity.get("last_name"):
        name_bit = f"{identity.get('first_name', '')} {identity.get('last_name', '')}".strip() or name_bit

    hd_yes = bool(profile_meta.get("full_res") or profile_meta.get("hd"))
    return {
        "gender": gender or "unknown",
        "nationality": nationality or "unknown",
        "age_guess": age_guess or "unknown",
        "full_name": identity.get("full_name") or "",
        "first_name": identity.get("first_name") or "",
        "last_name": identity.get("last_name") or "",
        "evidence": "; ".join(dict.fromkeys(evidence)) or "thin public signal",
        "photo_ok": "yes" if photo.get("ok") else "no",
        "photo_note": str(photo.get("note") or ""),
        "vision_photos": str(photo.get("photos_used") or len(photo.get("person_paths") or []) or 0),
        "name_display": name_bit,
        "followers": str(followers),
        "is_kol": "yes" if is_kol else "no",
        "kol_niche": str(research.get("kol_niche") or ("creator" if is_kol else "none")),
        "visibility": visibility,
        "profile_hd": "yes" if hd_yes else "no",
        "profile_wxh": f"{profile_meta.get('width', 0)}x{profile_meta.get('height', 0)}",
        "profile_bytes": str(profile_meta.get("bytes") or 0),
        "feed_count": str(len(feed_rels)),
        "pin_count": str(len(pin_rels) if visibility != "private" else 0),
        "pipeline": " > ".join(steps),
    }


def resolve_member_profile(handle: str) -> dict[str, Any]:
    """
    Full onboarding research pipeline:
      1) Web search + DeepSeek (KOL / gender / locale)
      2) IG scrape (public HD+3 feed / private low-res)
      3) Demographics fusion
    """
    handle = normalize_handle(handle)
    research = research_handle_before_ig(handle)
    scrape = scrape_instagram_bio(handle, pre_web=research, skip_web=True)
    scraped = scrape.get("text") or f"instagram_handle:{handle}"
    demo = infer_demographics(
        scraped,
        scrape=scrape,
        handle=handle,
        ig_photo_path=scrape.get("ig_photo_path") or "",
    )
    return {
        "handle": handle,
        "research": research,
        "scrape": scrape,
        "demo": demo,
        "eligible": club_ai_eligible(demo),
    }


def format_demographics_line(demo: dict[str, str]) -> str:
    g = demo.get("gender") or "unknown"
    n = demo.get("nationality") or "unknown"
    a = demo.get("age_guess") or "unknown"
    name = demo.get("name_display") or demo.get("full_name") or ""
    bits = [f"**Profile guess:** {g} · {n} · {a}"]
    if name:
        bits.append(f"Name read: **{name}**")
    if demo.get("is_kol") == "yes":
        bits.append(f"_KOL: yes ({demo.get('kol_niche') or 'creator'}) · followers {demo.get('followers') or '?'}._")
    vis = demo.get("visibility") or ""
    if vis:
        hd = demo.get("profile_hd") or "no"
        bits.append(
            f"_IG {vis}: profile {demo.get('profile_wxh') or '?'} "
            f"(HD={hd}) · pins {demo.get('pin_count') or '0'} · "
            f"feed {demo.get('feed_count') or '0'}/{FEED_PHOTO_MAX}._"
        )
    vp = demo.get("vision_photos") or ""
    if demo.get("photo_ok") == "yes" and vp:
        bits.append(f"_Vision: {vp} photo(s)._")
    elif demo.get("photo_ok") == "no":
        bits.append(f"_Vision: unavailable — {(demo.get('photo_note') or '')[:80]}_")
    ev = demo.get("evidence") or ""
    if ev:
        short = ev if len(ev) < 220 else ev[:217] + "…"
        bits.append(f"_Signals: {short}_")
    bits.append("_Pipeline: web/KOL → IG photos → name/bio — estimate, not verified._")
    return "\n".join(bits)


def _nationality_allowed(nationality: str) -> bool:
    n = (nationality or "").strip().lower()
    if not n or n == "unknown":
        return False
    if any(k in n for k in _ALLOWED_NAT_KEYS):
        return True
    aliases = {
        "hk": "hong kong",
        "roc": "taiwan",
        "prc": "china",
        "rok": "korea",
        "sg": "singapore",
    }
    return aliases.get(n, "") in _ALLOWED_NAT_KEYS or n in aliases


def _nationality_explicitly_disallowed(nationality: str) -> bool:
    """True only when we positively detected a locale outside the club focus."""
    n = (nationality or "").strip().lower()
    if not n or n == "unknown":
        return False
    if _nationality_allowed(n):
        return False
    blocked = (
        "united states", "usa", "america", "united kingdom", "britain", "england",
        "australia", "canada", "france", "germany", "india", "philippines",
        "malaysia", "indonesia", "thailand", "vietnam", "brazil", "mexico",
        "russia", "italy", "spain", "europe", "middle east", "africa",
    )
    return any(b in n for b in blocked)


def _age_under_forty(age_guess: str) -> bool:
    """True when the age signal is clearly under 40. Ranges like 25-34 count."""
    s = (age_guess or "").strip().lower().replace("–", "-").replace("—", "-")
    if not s or s in {"unknown", "n/a", "na", "?"}:
        return False
    if any(k in s for k in ("senior", "40s", "50s", "60s", "70s", "80s", "over 40", "40+", "40 +")):
        return False
    if any(k in s for k in ("under 40", "below 40", "<40", "< 40")):
        return True
    nums = [int(x) for x in re.findall(r"\d{2}", s)]
    if nums:
        return all(n < 40 for n in nums)
    return any(
        k in s
        for k in (
            "teen", "early 20", "late 20", "early 30", "late 30",
            "20s", "30s", "early-mid 20",
        )
    )


def club_ai_eligible(demo: dict[str, str]) -> tuple[bool, str]:
    """
    In only when both hold: female, and age clearly under 40.
    Unknown gender or age is gated. Nationality is not a gate.
    """
    gender = (demo.get("gender") or "").strip().lower()
    if gender != "female":
        return False, "gender"
    if not _age_under_forty(demo.get("age_guess") or ""):
        return False, "age"
    return True, ""


def _gate_check_lines(demo: dict[str, str]) -> str:
    gender = (demo.get("gender") or "unknown").strip() or "unknown"
    age = (demo.get("age_guess") or "unknown").strip() or "unknown"
    g_ok = gender.lower() == "female"
    a_ok = _age_under_forty(age)
    return (
        f"- Gender: {gender} — {'pass' if g_ok else 'fail (need female)'}\n"
        f"- Age: {age} — {'pass' if a_ok else 'fail (need clearly under 40)'}"
    )


def describe_gate(
    demo: dict[str, str],
    *,
    override: Optional[bool],
    auto_ok: bool,
    auto_reason: str,
    final_ok: bool,
) -> str:
    checks = _gate_check_lines(demo)
    fails = {
        "gender": "gender is not female",
        "age": "age is not clearly under 40",
    }
    fail = fails.get(auto_reason or "", auto_reason or "a check failed")
    if override is True:
        head = "Admin forced them in. The automatic check is ignored."
    elif override is False:
        head = "Admin forced them out. The 25% roll does not apply."
    elif auto_ok and final_ok:
        head = "Gated in. Gender and age both passed."
    elif (not auto_ok) and final_ok:
        head = f"Automatic gate was out ({fail}). Let in on the 25% roll."
    elif not auto_ok:
        head = f"Gated out. {fail[0].upper() + fail[1:]}."
    else:
        head = "Checks would pass, but they are marked out."
    return f"{head}\n{checks}"


def settle_gate(handle: str, demo: dict[str, str]) -> tuple[bool, str]:
    """Apply admin lock, then the silent 25% roll. Returns (in?, admin-only explanation)."""
    if normalize_handle(handle) in ADMIN_HANDLES:
        return True, "Admin account. The gate does not apply."
    auto_ok, auto_reason = club_ai_eligible(demo)
    override = gate_override_for(handle)
    after_admin = auto_ok if override is None else bool(override)
    final = maybe_lucky_in(handle, after_admin)
    detail = describe_gate(
        demo,
        override=override,
        auto_ok=auto_ok,
        auto_reason=auto_reason,
        final_ok=final,
    )
    return final, detail


def gate_story_for_admin(user: dict) -> str:
    if is_admin(user):
        return "Admin account. The gate does not apply."
    demo = {
        "gender": user.get("gender") or "",
        "nationality": user.get("nationality") or "",
        "age_guess": user.get("age_guess") or "",
    }
    if not any(v.strip() for v in demo.values()):
        stored = (user.get("gate_detail") or "").strip()
        return stored or "No gender or age saved yet."
    auto_ok, auto_reason = club_ai_eligible(demo)
    raw = user.get("gate_override")
    override = None if raw is None else bool(int(raw))
    if override is True:
        final = True
    elif override is False:
        final = False
    else:
        ai = user.get("ai_enabled")
        final = bool(int(ai)) if ai is not None else auto_ok
    return describe_gate(
        demo,
        override=override,
        auto_ok=auto_ok,
        auto_reason=auto_reason,
        final_ok=final,
    )


def character_why_for_admin(user: dict) -> str:
    stored = (user.get("assign_why") or "").strip()
    if stored:
        return stored
    vibe = (user.get("vibe") or "").strip()
    if not vibe:
        return "No assignment notes saved for this account."
    vibe = re.split(r"\n\nPrivate account|\n\nAlso peeked|\n\nBio emojis", vibe)[0].strip()
    why = re.search(r"(\*\*Why .+?\*\*\n[\s\S]+)", vibe)
    if why:
        return why.group(1).strip()
    return vibe[:600]


def assign_club_tennis() -> tuple[str, str, str, str, str]:
    """Fallback identity: club ball avatar (looks like a normal assignment)."""
    return (
        CLUB_TENNIS_LABEL,
        "Here’s your **club tennis** ball — let’s get you a PIN and onto the court.",
        CLUB_TENNIS_EMOJI,
        CLUB_TENNIS_LABEL,
        CLUB_TENNIS_FILE,
    )


def user_ai_enabled(user: Optional[dict] = None) -> bool:
    u = user or st.session_state.get("user")
    if not u:
        return False
    if is_admin(u):
        return True
    val = u.get("ai_enabled")
    if val is None:
        return True
    return bool(int(val)) if not isinstance(val, bool) else val


def format_api_error(exc: Exception) -> str:
    """Turn provider errors into something a member can act on."""
    status = getattr(exc, "status_code", None)
    message = ""
    body = getattr(exc, "body", None)
    if isinstance(body, dict):
        err = body.get("error") or body
        if isinstance(err, dict):
            message = str(err.get("message") or "")
    if not message:
        message = str(exc)
    text = f"{message}".lower()
    model = os.environ.get("DEEPSEEK_MODEL", DEEPSEEK_MODEL)

    if status == 402 or "insufficient balance" in text:
        return (
            "API says **Insufficient Balance**. Top up credit or update "
            "`DEEPSEEK_API_KEY` in `.env`, then refresh."
        )
    if status in (401, 403) or "incorrect api key" in text or "invalid api key" in text:
        return (
            "API rejected the key (auth error). Confirm `.env` has the NewCoin key, "
            f"base `{os.environ.get('DEEPSEEK_BASE_URL', DEEPSEEK_BASE_URL)}`, "
            "then fully restart Streamlit."
        )
    if status == 404 or ("model" in text and ("not found" in text or "does not exist" in text)):
        return f"Model `{model}` wasn’t recognized. Check `DEEPSEEK_MODEL` in `.env`."
    # Surface a short real reason so we don't mislabel unrelated failures as bad keys
    short = message.replace("\n", " ").strip()
    if len(short) > 180:
        short = short[:177] + "…"
    return f"API error ({type(exc).__name__}" + (f" {status}" if status else "") + f"): {short}"


def local_tennis_reply(user_text: str) -> str:
    """Offline schedule answers when the API is unavailable."""
    lower = (user_text or "").lower()
    games = list_games()
    off_topic = any(
        w in lower
        for w in (
            "python", "code", "program", "weather", "news", "stock", "bitcoin",
            "recipe", "politics", "movie",
        )
    )
    if off_topic:
        return (
            "I only talk tennis, schedules, and the club. "
            "Ask me what’s on the board or how many spots are left."
        )
    if not games:
        return (
            "No games are scheduled yet. "
            f"An admin can add one in chat — e.g. `Add game Sat 3pm 4 spots {DEFAULT_GAME_LOCATION}`."
        )
    return "Here's the current board:\n\n" + games_as_context()


def scrub_future_game_promises(text: str) -> str:
    """Drop offers to flag or notify later. The chat is not always open."""
    raw = text or ""
    cleaned = re.sub(
        r"[^.?!\n]*\b("
        r"flag you|notify you|ping you|alert you|"
        r"let you know|message you|watch for|when the next game|"
        r"when a game is posted|once a game is posted"
        r")\b[^.?!\n]*[.?!]?",
        "",
        raw,
        flags=re.I,
    )
    cleaned = re.sub(r"[ \t]+\n", "\n", cleaned)
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned).strip()
    if cleaned:
        return cleaned
    if list_games():
        return "Ask me what’s on the board."
    return "No games are scheduled right now."


def deepseek_chat(messages: list[dict[str, str]], extra_system: str = "") -> str:
    client = get_client()
    system = SYSTEM_PROMPT
    if extra_system:
        system = SYSTEM_PROMPT + "\n\n" + extra_system

    last_user = ""
    for msg in reversed(messages):
        if msg.get("role") == "user":
            last_user = msg.get("content") or ""
            break

    if client is None:
        return (
            "DeepSeek API key missing — set `DEEPSEEK_API_KEY` in `.env` or Streamlit secrets.\n\n"
            + local_tennis_reply(last_user)
        )

    api_messages = [{"role": "system", "content": system}] + messages
    try:
        completion = client.chat.completions.create(
            model=active_model(),
            messages=api_messages,
            temperature=0.4,
            max_tokens=MAX_TOKENS,
        )
        text = completion_text(completion) or "Serve again?"
        return scrub_future_game_promises(text)
    except Exception as exc:
        return format_api_error(exc) + "\n\n" + local_tennis_reply(last_user)

def parse_add_game(text: str) -> Optional[dict]:
    """Parse admin add-game intent via DeepSeek, with regex fallback.

    Returns a dict with when_text / location / spots / notes / spots_set,
    or None if this is not an add-game command.
    """
    client = get_client()
    if client:
        try:
            completion = client.chat.completions.create(
                model=active_model(),
                messages=[
                    {
                        "role": "system",
                        "content": (
                            "Parse tennis game admin commands. Return ONLY JSON: "
                            '{"action":"add_game"|"none","when_text":"date and time together",'
                            '"location":"...","spots":4,"notes":"..."}. '
                            "when_text must include both a date (weekday or calendar date) and a time. "
                            "spots is required for add_game. "
                            "If location is missing, use an empty string. "
                            "Example input: Add game Sat 3pm 4 spots Happy Valley"
                        ),
                    },
                    {"role": "user", "content": text},
                ],
                temperature=0.1,
                max_tokens=MAX_TOKENS,
            )
            raw = completion_text(completion)
            raw = re.sub(r"^```(?:json)?\s*|\s*```$", "", raw, flags=re.I).strip()
            data = json.loads(raw)
            if str(data.get("action", "")).lower() == "add_game":
                spots_raw = data.get("spots", None)
                spots_set = spots_raw is not None and str(spots_raw).strip() != ""
                try:
                    spots = int(spots_raw) if spots_set else 0
                except (TypeError, ValueError):
                    spots = 0
                    spots_set = False
                return {
                    "when_text": str(data.get("when_text") or "").strip(),
                    "location": str(data.get("location") or "").strip(),
                    "spots": max(1, spots) if spots_set else 0,
                    "spots_set": spots_set,
                    "notes": str(data.get("notes") or "").strip(),
                }
        except Exception:
            pass

    return _heuristic_add_game(text)


def _heuristic_add_game(text: str) -> Optional[dict]:
    lower = text.lower().strip()
    if not re.search(r"\badd\s+(a\s+)?game\b", lower):
        return None

    spots = 0
    spots_set = False
    m_spots = re.search(r"(\d+)\s*spots?", text, re.I)
    if m_spots:
        spots = int(m_spots.group(1))
        spots_set = True

    cleaned = re.sub(r"^(please\s+)?add\s+(a\s+)?game\s+", "", text.strip(), flags=re.I)
    cleaned = re.sub(r"\s+\d+\s*spots?\b", "", cleaned, flags=re.I).strip()
    cleaned = re.sub(r"\s+spots?\b", "", cleaned, flags=re.I).strip()

    location = ""
    m_loc = re.search(r"\b(?:at|@|in)\s+(.+)$", cleaned, re.I)
    if m_loc:
        location = m_loc.group(1).strip(" .,")
        cleaned = cleaned[: m_loc.start()].strip()
    else:
        # Trailing multi-word place (e.g. Happy Valley) after time token
        m_place = re.search(
            r"((?:a\.?m\.?|p\.?m\.?|\d{1,2}:\d{2}|\d{1,2})\s+)([A-Za-z][A-Za-z .'-]{2,})$",
            cleaned,
            re.I,
        )
        if m_place and not _GAME_TIME_RE.search(m_place.group(2)):
            location = m_place.group(2).strip(" .,")
            cleaned = cleaned[: m_place.start(2)].strip()

    when_text = cleaned.strip(" ,.-")
    return {
        "when_text": when_text,
        "location": location,
        "spots": max(1, spots) if spots_set else 0,
        "spots_set": spots_set,
        "notes": "",
    }


def finalize_add_game(parsed: dict) -> tuple[Optional[dict], Optional[str]]:
    """Validate add-game fields. Location defaults to Happy Valley."""
    when_text = (parsed.get("when_text") or "").strip()
    location = (parsed.get("location") or "").strip() or DEFAULT_GAME_LOCATION
    spots_set = bool(parsed.get("spots_set"))
    try:
        spots = int(parsed.get("spots") or 0)
    except (TypeError, ValueError):
        spots = 0
        spots_set = False

    missing: list[str] = []
    if not when_text or not _GAME_DATE_RE.search(when_text):
        missing.append("date")
    if not when_text or not _GAME_TIME_RE.search(when_text):
        missing.append("time")
    if not spots_set or spots < 1:
        missing.append("spots")

    if missing:
        need = ", ".join(f"**{m}**" for m in missing)
        return None, (
            f"Almost — still need {need}. Location defaults to **{DEFAULT_GAME_LOCATION}** "
            "if you skip it.\n\n"
            f"Example: `Add game Sat 3pm 4 spots {DEFAULT_GAME_LOCATION}`"
        )

    return {
        "when_text": when_text,
        "location": location,
        "spots": spots,
        "notes": str(parsed.get("notes") or "").strip(),
    }, None


def parse_admin_quick_login(text: str) -> Optional[tuple[str, str]]:
    """Match `@handle 1234` for admin one-line login. Returns (handle, pin) or None."""
    m = re.fullmatch(r"@([A-Za-z0-9._]{2,30})\s+(\d{4})", (text or "").strip())
    if not m:
        return None
    handle = normalize_handle(m.group(1))
    if handle not in ADMIN_HANDLES:
        return None
    return handle, m.group(2)


def rewrite_last_user(content: str) -> None:
    msgs = st.session_state.get("messages") or []
    if msgs and msgs[-1].get("role") == "user":
        msgs[-1]["content"] = content


def plain_site_name(text: str) -> str:
    """Keep site name readable without markdown code/link styling."""
    if not isinstance(text, str):
        return text
    # Zero-width spaces stop Streamlit/markdown from auto-linking the domain.
    plain = "www\u200b.playplaytennis\u200b.com"
    return (
        text.replace("`www.playplaytennis.com`", plain)
        .replace("www.playplaytennis.com", plain)
    )


# ---------------------------------------------------------------------------
# Session / UI
# ---------------------------------------------------------------------------


def ensure_session() -> None:
    defaults: dict[str, Any] = {
        "auth_state": NEED_IG,
        "pending_handle": "",
        "pending_animal": "",
        "pending_vibe": "",
        "pending_emoji": "🎾",
        "pending_mascot": "",
        "pending_avatar": "",
        "pending_ig_photo": "",
        "handle_locked": False,
        "locked_handle": "",
        "user": None,
        "messages": [],
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v


def assistant_avatar() -> str:
    """Robot before login; club tennis photo after login."""
    if st.session_state.get("auth_state") == LOGGED_IN and st.session_state.get("user"):
        return club_avatar()
    return "🤖"


def append_assistant(
    content: str,
    avatar: Optional[str] = None,
    image: Optional[str] = None,
    ig_photo: Optional[str] = None,
) -> None:
    msg: dict[str, Any] = {
        "role": "assistant",
        "content": content,
        "avatar": avatar or assistant_avatar(),
    }
    if image:
        msg["image"] = image
    if ig_photo:
        msg["ig_photo"] = ig_photo
    st.session_state.messages.append(msg)


def append_user(content: str, avatar: Optional[str] = None) -> None:
    st.session_state.messages.append(
        {"role": "user", "content": content, "avatar": avatar or "👤"}
    )


def user_avatar(user: Optional[dict] = None) -> str:
    u = user or st.session_state.get("user")
    if not u:
        return "👤"
    return animal_photo_path(u.get("mascot") or u.get("animal"), u.get("avatar_path"))


def _file_to_data_uri(path: str) -> str:
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError:
        return ""
    ext = path.rsplit(".", 1)[-1].lower()
    mime = {
        "png": "image/png",
        "jpg": "image/jpeg",
        "jpeg": "image/jpeg",
        "webp": "image/webp",
        "gif": "image/gif",
        "mp4": "video/mp4",
    }.get(ext, "image/png")
    return f"data:{mime};base64,{base64.b64encode(raw).decode('ascii')}"


_MEDIA_URI_CACHE: dict[str, str] = {}


def _hosted_media_url(path: str) -> str:
    """Inline a local image or video so the hosted site can show it.

    Streamlit Community Cloud answers /app/static/... with a login redirect,
    so a video or img pointed there stays blank even after you open the app.
    """
    if not path or not os.path.isfile(path):
        return ""
    cached = _MEDIA_URI_CACHE.get(path)
    if cached:
        return cached
    uri = _file_to_data_uri(path)
    if uri:
        _MEDIA_URI_CACHE[path] = uri
    return uri


def resolve_media_path(path: Optional[str]) -> str:
    if not path:
        return ""
    full = path if os.path.isabs(path) else os.path.join(AVATAR_DIR, path)
    return full if os.path.isfile(full) else ""


def ig_profile_rel(user: Optional[dict]) -> str:
    """Saved IG profile photo for a member, including profiles/{handle}.jpg if the DB path is empty."""
    if not user:
        return ""
    stored = (user.get("ig_photo_path") or "").strip()
    if resolve_media_path(stored):
        return stored
    handle = normalize_handle(user.get("ig_handle") or "")
    if not handle:
        return ""
    for ext in ("jpg", "jpeg", "png", "webp"):
        rel = f"profiles/{handle}.{ext}"
        if resolve_media_path(rel):
            return rel
    return ""


def render_character_hero(path: str) -> None:
    """Full-size character portrait via HTML so chat avatar CSS cannot shrink it."""
    full = resolve_media_path(path)
    if not full:
        return
    uri = _file_to_data_uri(full)
    if not uri:
        return
    st.markdown(
        f'<div class="character-hero mascot-zoom">'
        f'<img src="{uri}" alt="character" /></div>',
        unsafe_allow_html=True,
    )


def focus_chat_input() -> None:
    """Put the caret back in chat_input after each send/rerun."""
    # Bump a nonce so the script re-executes every run
    st.session_state["_focus_nonce"] = st.session_state.get("_focus_nonce", 0) + 1
    nonce = st.session_state["_focus_nonce"]
    try:
        import streamlit.components.v1 as components

        components.html(
            f"""
            <div style="height:0;overflow:hidden">{nonce}</div>
            <script>
              (function() {{
                const nonce = {nonce};
                function focusChat() {{
                  const doc = window.parent.document;
                  const nodes = doc.querySelectorAll(
                    '[data-testid="stChatInput"] textarea, [data-testid="stChatInputTextArea"]'
                  );
                  if (!nodes.length) return false;
                  const el = nodes[nodes.length - 1];
                  el.focus({{ preventScroll: true }});
                  try {{
                    const len = el.value ? el.value.length : 0;
                    el.setSelectionRange(len, len);
                  }} catch (e) {{}}
                  return true;
                }}
                function bindCritters() {{
                  const doc = window.parent.document;
                  function hidePop() {{
                    doc.querySelectorAll(".critter-pop").forEach(function(node) {{ node.remove(); }});
                    doc._ltPopEl = null;
                  }}
                  function showPop(el) {{
                    if (!el || doc._ltPopEl === el) return;
                    hidePop();
                    doc._ltPopEl = el;
                    const img = el.tagName === "IMG" ? el : el.querySelector("img");
                    const rect = el.getBoundingClientRect();
                    const pop = img ? doc.createElement("img") : doc.createElement("div");
                    pop.className = "critter-pop";
                    if (img && img.src) {{
                      pop.src = img.src;
                      pop.alt = "";
                    }} else {{
                      pop.textContent = (el.innerText || "").trim().slice(0, 8);
                      pop.style.display = "flex";
                      pop.style.alignItems = "center";
                      pop.style.justifyContent = "center";
                      pop.style.fontSize = "64px";
                      pop.style.background = "#fff";
                    }}
                    const size = 128;
                    const gap = 10;
                    const vw = doc.documentElement.clientWidth;
                    const vh = doc.documentElement.clientHeight;
                    const input = doc.querySelector('[data-testid="stChatInput"]');
                    const floor = input ? input.getBoundingClientRect().top - 8 : vh - 8;
                    let left = rect.left + rect.width / 2 - size / 2;
                    left = Math.max(8, Math.min(left, vw - size - 8));
                    let top = rect.bottom + gap;
                    if (top + size > floor) {{
                      top = Math.max(8, Math.min(rect.top + rect.height / 2 - size / 2, floor - size));
                      if (vw - rect.right >= rect.left) left = Math.min(rect.right + gap, vw - size - 8);
                      else left = Math.max(8, rect.left - size - gap);
                    }}
                    pop.style.left = left + "px";
                    pop.style.top = top + "px";
                    doc.body.appendChild(pop);
                  }}
                  function hoverEl(node) {{
                    if (!node || !node.closest) return null;
                    if (node.closest(".critter-pop") || node.closest(".lt-film") || node.closest(".lt-stage")) return null;
                    const critter = node.closest(".critter");
                    if (critter) return critter;
                    const msg = node.closest('[data-testid="stChatMessage"]');
                    if (!msg) return null;
                    const avatar = msg.querySelector('[data-testid*="Avatar"], [data-testid*="avatar"]') || msg.firstElementChild;
                    if (avatar && (avatar === node || avatar.contains(node))) return avatar;
                    return null;
                  }}
                  doc._ltHover = function(ev) {{
                    const el = hoverEl(ev.target);
                    if (!el) return;
                    showPop(el);
                  }};
                  doc._ltLeave = function(ev) {{
                    const el = hoverEl(ev.target);
                    if (!el) return;
                    const next = ev.relatedTarget;
                    if (next && el.contains(next)) return;
                    hidePop();
                  }};
                  if (doc._ltOverFn) doc.removeEventListener("mouseover", doc._ltOverFn, true);
                  if (doc._ltOutFn) doc.removeEventListener("mouseout", doc._ltOutFn, true);
                  doc._ltOverFn = function(ev) {{ if (doc._ltHover) doc._ltHover(ev); }};
                  doc._ltOutFn = function(ev) {{ if (doc._ltLeave) doc._ltLeave(ev); }};
                  doc.addEventListener("mouseover", doc._ltOverFn, true);
                  doc.addEventListener("mouseout", doc._ltOutFn, true);
                  const scroller = doc.querySelector('[data-testid="stAppScrollToBottomContainer"]');
                  if (scroller && scroller.dataset.popbound !== "1") {{
                    scroller.dataset.popbound = "1";
                    scroller.addEventListener("scroll", hidePop);
                  }}
                }}
                function bindFilm() {{
                  const doc = window.parent.document;
                  const video = doc.querySelector(".lt-film");
                  const btn = doc.querySelector(".lt-sound");
                  if (!video || !btn || video.dataset.bound === "1") return;
                  video.dataset.bound = "1";
                  video.loop = false;
                  video.muted = false;
                  function paint() {{
                    const on = !video.muted;
                    btn.setAttribute("aria-pressed", on ? "true" : "false");
                    btn.textContent = on ? "Mute" : "Sound";
                    btn.setAttribute("aria-label", on ? "Mute sound" : "Turn sound on");
                  }}
                  video.addEventListener("ended", function() {{
                    video.pause();
                    const end = Math.max(0, (video.duration || 0) - 0.05);
                    if (end) {{
                      try {{ video.currentTime = end; }} catch (e) {{}}
                    }}
                  }});
                  btn.addEventListener("click", function() {{
                    video.muted = !video.muted;
                    if (video.paused && video.currentTime < (video.duration || 1) - 0.2) {{
                      video.play().catch(function() {{}});
                    }}
                    paint();
                  }});
                  const started = video.play();
                  if (started && started.then) {{
                    started.then(function() {{ paint(); }}).catch(function() {{
                      video.muted = false;
                      paint();
                      function startWithSound() {{
                        video.muted = false;
                        video.play().then(paint).catch(function() {{}});
                      }}
                      doc.addEventListener("pointerdown", startWithSound, {{ once: true, capture: true }});
                    }});
                  }}
                  paint();
                }}
                let tries = 0;
                const timer = setInterval(function() {{
                  tries += 1;
                  bindCritters();
                  bindFilm();
                  if ((focusChat() && docHasCritters()) || tries > 24) clearInterval(timer);
                }}, 50);
                function docHasCritters() {{
                  return window.parent.document.querySelectorAll(".critter").length > 0;
                }}
              }})();
            </script>
            """,
            height=0,
            width=0,
        )
    except Exception:
        pass


def inject_styles() -> None:
    st.markdown(
        """
        <style>
          @import url('https://fonts.googleapis.com/css2?family=Manrope:wght@400;500;600;700&display=swap');
          :root { --chat-w: min(720px, calc(100vw - 32px)); }
          html, body, .stApp {
            font-family: "Manrope", "Segoe UI", sans-serif;
            color: #1a1f1c;
            background: #f6f5f2 !important;
            height: 100%;
          }
          [data-testid="stAppViewContainer"],
          [data-testid="stMain"],
          [data-testid="stMainBlockContainer"] {
            background: transparent !important;
          }
          #MainMenu, footer, [data-testid="stToolbar"],
          [data-testid="stDecoration"], [data-testid="stStatusWidget"],
          [data-testid="stAppDeployButton"], .stDeployButton,
          [data-testid="stHeaderActionElements"],
          div[class*="viewerBadge"], a[href*="streamlit.io"],
          a[href*="streamlitapp.com"], a[href*="share.streamlit.io"],
          [data-testid="stBaseButton-header"],
          [data-testid="stBaseButton-headerNoPadding"],
          button[kind="header"],
          .stAppDeployButton,
          div[data-testid="stActionButtonIcon"] {
            display: none !important;
            visibility: hidden !important;
            pointer-events: none !important;
            width: 0 !important;
            height: 0 !important;
            overflow: hidden !important;
          }
          header[data-testid="stHeader"] {
            background: transparent !important;
            height: 0 !important;
            min-height: 0 !important;
          }

          [data-testid="stAppScrollToBottomContainer"] {
            height: calc(100dvh - 84px) !important;
            max-height: calc(100dvh - 84px) !important;
            overflow-y: auto !important;
            overflow-x: hidden !important;
            display: flex !important;
            flex-direction: column !important;
          }
          [data-testid="stAppScrollToBottomContainer"]::-webkit-scrollbar { width: 8px; }
          [data-testid="stAppScrollToBottomContainer"]::-webkit-scrollbar-thumb {
            background: rgba(28, 40, 34, 0.22);
            border-radius: 99px;
          }
          [data-testid="stAppScrollToBottomContainer"] > div:empty {
            display: none !important;
            flex: none !important;
            height: 0 !important;
            min-height: 0 !important;
          }
          [data-testid="stMainBlockContainer"] {
            flex: 1 1 auto;
            display: flex !important;
            flex-direction: column !important;
          }
          .block-container {
            max-width: var(--chat-w) !important;
            width: var(--chat-w);
            background: transparent !important;
            border: 0 !important;
            box-shadow: none !important;
            border-radius: 0 !important;
            margin: 0 auto !important;
            padding: 0.45rem 0.15rem 0.2rem !important;
            min-height: calc(100dvh - 84px) !important;
            box-sizing: border-box !important;
            display: flex !important;
            flex-direction: column !important;
          }
          [data-testid="stVerticalBlock"] {
            flex: 1 1 auto;
            display: flex !important;
            flex-direction: column !important;
            gap: 0.9rem !important;
          }
          [data-testid="stChatMessage"] [data-testid="stVerticalBlock"] {
            flex: 0 0 auto !important;
            gap: 1.05rem !important;
            min-height: 0 !important;
          }
          [data-testid="stVerticalBlock"] > :has([data-testid="stChatMessage"]) {
            margin-top: auto !important;
          }
          [data-testid="stVerticalBlock"] > :has([data-testid="stChatMessage"]) ~ :has([data-testid="stChatMessage"]) {
            margin-top: 0 !important;
          }
          [data-testid="stBottom"] {
            position: fixed !important;
            left: 0 !important;
            right: 0 !important;
            bottom: 0 !important;
            top: auto !important;
            height: auto !important;
            z-index: 1000 !important;
            background: #f6f5f2 !important;
            padding: 0 0 max(0.7rem, env(safe-area-inset-bottom)) !important;
            margin: 0 !important;
          }
          [data-testid="stBottomBlockContainer"] {
            max-width: var(--chat-w) !important;
            width: var(--chat-w);
            background: transparent !important;
            border: 0 !important;
            box-shadow: none !important;
            border-radius: 0 !important;
            margin: 0 auto !important;
            padding: 0 0.2rem !important;
          }

          .stMarkdown, [data-testid="stChatMessageContent"] {
            font-family: "Manrope", "Segoe UI", sans-serif;
            color: #1c2822;
            line-height: 1.6;
            letter-spacing: -0.011em;
          }
          [data-testid="stChatMessageContent"] p { margin: 0 0 0.55rem; }
          [data-testid="stChatMessageContent"] p:last-child { margin-bottom: 0; }
          [data-testid="stChatMessageContent"] a { color: #244033; }
          [data-testid="stLayoutWrapper"],
          [data-testid="stElementContainer"],
          [data-testid="stVerticalBlock"],
          [data-testid="stChatMessage"] {
            min-width: 0 !important;
            max-width: 100% !important;
          }
          [data-testid="stChatMessage"] {
            background: transparent !important;
            border-radius: 0 !important;
            padding: 0.35rem 0 !important;
            margin: 0 !important;
            box-shadow: none !important;
            align-items: flex-start !important;
            gap: 0.75rem !important;
            width: 100% !important;
            box-sizing: border-box !important;
          }
          [data-testid="stChatMessageContent"] {
            min-width: 0 !important;
            max-width: 100% !important;
            overflow-wrap: break-word;
          }
          [data-testid="stChatMessageContent"] p,
          [data-testid="stChatMessageContent"] li {
            overflow-wrap: break-word;
          }
          [data-testid="stChatMessageContent"] code {
            font-family: "Manrope", "Segoe UI", sans-serif !important;
            font-size: 1em !important;
            background: transparent !important;
            padding: 0 !important;
            white-space: normal !important;
          }
          [data-testid="stChatMessageContent"] a {
            color: #244033 !important;
            text-decoration: underline !important;
            pointer-events: auto !important;
          }
          [data-testid="stChatMessageAvatarAssistant"],
          [data-testid="stChatMessageAvatarUser"] {
            width: 28px !important;
            height: 28px !important;
            min-width: 28px !important;
            background: #e7efe9 !important;
            overflow: visible !important;
            cursor: zoom-in;
          }
          [data-testid="stChatMessage"] img {
            cursor: zoom-in;
          }

          [data-testid="stChatInput"] {
            position: relative !important;
            z-index: 1001 !important;
            background: #ffffff !important;
            border: 1px solid rgba(26, 31, 28, 0.12) !important;
            border-radius: 14px !important;
            box-shadow: 0 8px 24px rgba(26, 31, 28, 0.06) !important;
            max-height: 64px !important;
            overflow: hidden !important;
          }
          [data-testid="stChatInput"]:focus-within {
            border-color: #3d5c4a !important;
            box-shadow: 0 0 0 4px rgba(61, 92, 74, 0.14) !important;
          }
          [data-testid="stChatInputTextArea"] {
            font-family: "Manrope", "Segoe UI", sans-serif !important;
            color: #1c2822 !important;
            font-size: 0.98rem !important;
            max-height: 40px !important;
            overflow-y: auto !important;
            resize: none !important;
          }
          [data-testid="stChatInputSubmitButton"] {
            background: #3d5c4a !important;
            color: #f7f4ef !important;
            border-radius: 12px !important;
            position: relative !important;
            z-index: 1002 !important;
          }
          [data-testid="stChatInputSubmitButton"]:hover { background: #314a3c !important; }
          [data-testid="stAlert"] {
            background: rgba(255, 252, 248, 0.94) !important;
            border-radius: 14px !important;
            color: #1c2822 !important;
          }

          .lt-head {
            display: flex;
            flex-direction: column;
            gap: 0.55rem;
            margin: 0 0 0.35rem;
          }
          .lt-brand {
            margin: 0 0 0.15rem;
            text-align: center;
            font-size: 1.35rem !important;
            font-weight: 700;
            letter-spacing: 0.01em;
            color: #3d5c4a;
            line-height: 1.25;
          }
          .lt-stage { position: relative; }
          .lt-film {
            width: 100%;
            height: 90px;
            object-fit: cover;
            object-position: center 42%;
            border-radius: 12px;
            display: block;
            background: #1c2822;
            box-shadow: 0 8px 20px rgba(20, 32, 24, 0.08);
          }
          .lt-sound {
            position: absolute;
            right: 0.4rem;
            bottom: 0.4rem;
            border: 0;
            border-radius: 999px;
            padding: 0.18rem 0.5rem;
            background: rgba(247, 244, 239, 0.94);
            color: #1c2822;
            font-family: "Manrope", "Segoe UI", sans-serif;
            font-size: 0.62rem;
            font-weight: 600;
            letter-spacing: 0.06em;
            text-transform: uppercase;
            cursor: pointer;
          }
          .lt-sound[aria-pressed="true"] {
            background: #3d5c4a;
            color: #f7f4ef;
          }
          .lt-rail {
            display: flex;
            flex-wrap: nowrap;
            justify-content: center;
            gap: 0.55rem;
            margin: 0;
            padding: 0.2rem 0 0.35rem;
            overflow: visible;
            border-bottom: 1px solid rgba(28, 40, 34, 0.08);
          }
          .critter {
            position: relative;
            width: clamp(34px, 7.2vw, 44px);
            height: clamp(34px, 7.2vw, 44px);
            flex: 0 0 clamp(34px, 7.2vw, 44px);
            padding: 0;
            border: 2px solid #ffffff;
            border-radius: 50%;
            background: #ffffff;
            box-shadow: 0 4px 10px rgba(20, 32, 24, 0.1);
            cursor: pointer;
            overflow: visible;
          }
          .critter img {
            width: 100%;
            height: 100%;
            object-fit: cover;
            border-radius: 50%;
            display: block;
            transition: transform 0.18s ease;
          }
          .critter:hover, .critter:focus-visible, .critter.is-open {
            z-index: 6;
            border-color: #3d5c4a;
            outline: none;
          }
          .critter:hover img, .critter:focus-visible img, .critter.is-open img {
            transform: scale(1.08);
          }
          .critter-pop {
            position: fixed;
            z-index: 80;
            width: 128px;
            height: 128px;
            object-fit: cover;
            border-radius: 16px;
            pointer-events: none;
            box-shadow: 0 16px 36px rgba(20, 28, 22, 0.26);
            border: 3px solid #ffffff;
          }
          [data-testid="stVerticalBlock"] { overflow: visible; }

          .character-hero {
            margin: 0 0 0.15rem;
          }
          .character-hero img {
            width: min(100%, 360px);
            max-width: 360px;
            border-radius: 14px;
            display: block;
          }
          .ig-photo-chip {
            display: flex;
            align-items: center;
            gap: 0.65rem;
            margin: 0 0 0.7rem;
          }
          .ig-photo-chip img {
            width: 120px;
            height: 120px;
            border-radius: 16px;
            object-fit: cover;
          }

          @media (max-width: 760px) {
            :root { --chat-w: calc(100vw - 20px); }
            .lt-film { height: 72px; }
            .lt-rail { gap: 0.35rem; }
            /* Lift chat bar above Streamlit Cloud / mobile chrome badges */
            [data-testid="stBottom"] {
              padding-bottom: calc(3.4rem + env(safe-area-inset-bottom)) !important;
              z-index: 1100 !important;
            }
            [data-testid="stBottomBlockContainer"] {
              padding-bottom: 0.35rem !important;
            }
            [data-testid="stAppScrollToBottomContainer"] {
              height: calc(100dvh - 132px) !important;
              max-height: calc(100dvh - 132px) !important;
            }
            .block-container {
              min-height: calc(100dvh - 132px) !important;
              padding-bottom: 0.8rem !important;
            }
          }
        </style>
        """,
        unsafe_allow_html=True,
    )


CRITTER_SPECS = ()


def choose_rail_avatars() -> list[str]:
    cached = st.session_state.get("_rail_avatars")
    if isinstance(cached, list) and cached:
        return cached
    names = [
        name
        for name in os.listdir(AVATAR_DIR)
        if name.lower().endswith((".png", ".jpg", ".jpeg", ".webp"))
    ]
    pick = random.sample(names, k=min(8, len(names))) if names else []
    st.session_state["_rail_avatars"] = pick
    return pick


def render_little_tennis_header() -> None:
    buttons: list[str] = []
    for name in choose_rail_avatars():
        label = os.path.splitext(name)[0].replace("_", " ")
        path = os.path.join(STATIC_DIR, "pool", name)
        if not os.path.isfile(path):
            path = os.path.join(AVATAR_DIR, name)
        src = _hosted_media_url(path)
        if not src:
            continue
        buttons.append(
            f'<button type="button" class="critter" aria-label="{label}">'
            f'<img src="{src}" alt="" />'
            f"</button>"
        )
    poster = _hosted_media_url(os.path.join(STATIC_DIR, "poster.jpg"))
    film = _hosted_media_url(os.path.join(STATIC_DIR, "video.mp4"))
    poster_attr = f' poster="{poster}"' if poster else ""
    src_attr = f' src="{film}"' if film else ""
    st.markdown(
        '<header class="lt-head">'
        '<p class="lt-brand">www.playplaytennis.com</p>'
        '<div class="lt-stage">'
        f'<video class="lt-film" playsinline preload="auto"{poster_attr}{src_attr}></video>'
        '<button type="button" class="lt-sound" aria-pressed="true" aria-label="Mute sound">Mute</button>'
        "</div>"
        f'<div class="lt-rail">{"".join(buttons)}</div>'
        "</header>",
        unsafe_allow_html=True,
    )


def render_messages() -> None:
    for msg in st.session_state.messages:
        if msg["role"] == "assistant":
            avatar = msg.get("avatar") or assistant_avatar()
        else:
            avatar = msg.get("avatar") or "👤"
        with st.chat_message(msg["role"], avatar=avatar):
            img = msg.get("image")
            if img:
                render_character_hero(img)
            text = plain_site_name(msg.get("content") or "")
            st.markdown(text)


def render_mascot_banner(user: dict) -> None:
    photo = animal_photo_path(user.get("mascot") or user.get("animal"), user.get("avatar_path"))
    animal = user.get("mascot") or user.get("animal") or "Player"
    handle = user.get("ig_handle") or ""
    admin = " · admin" if is_admin(user) else ""
    cols = st.columns([1, 4])
    with cols[0]:
        st.markdown('<div class="mascot-zoom">', unsafe_allow_html=True)
        if isinstance(photo, str) and os.path.isfile(photo):
            st.image(photo, width=BANNER_IMAGE_WIDTH)
        else:
            st.markdown(f"<div style='font-size:3rem'>{photo}</div>", unsafe_allow_html=True)
        st.markdown("</div>", unsafe_allow_html=True)
    with cols[1]:
        st.markdown(f"**{animal}**{admin}")
        st.caption(f"@{handle}")

QUOTES_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tennis_quotes.json")


def load_tennis_quotes() -> list[dict[str, str]]:
    try:
        with open(QUOTES_PATH, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list) and data:
            return data
    except Exception:
        pass
    return [
        {
            "title": "letsballs creed",
            "body": "Book the court. Bring the vibes. Leave the ego in the locker. Let’s balls.",
        }
    ]


def next_tennis_quote() -> dict[str, str]:
    quotes = load_tennis_quotes()
    idx = int(st.session_state.get("_quote_idx", 0)) % len(quotes)
    st.session_state["_quote_idx"] = idx + 1
    return quotes[idx]


def guest_tennis_story_reply(user_text: str = "", remind_ig: bool = True) -> str:
    """No-AI reply for guests / gated members."""
    q = next_tennis_quote()
    if remind_ig and not st.session_state.get("handle_locked"):
        tip = "\n\n—\nWhen you’re ready, drop your Instagram handle with an **@**."
    else:
        tip = ""
    return f"🎾 **{q['title']}**\n\n{q['body']}{tip}"


def bootstrap_greeting() -> None:
    if st.session_state.messages:
        return
    append_assistant(
        "Hey — welcome to www.playplaytennis.com.\n\n"
        "Drop your Instagram handle with an **@**."
    )


def _lock_handle_session(handle: str) -> None:
    """After a gated assignment, freeze this session — no new @ drops / reminders."""
    st.session_state.handle_locked = True
    st.session_state.locked_handle = normalize_handle(handle)
    st.session_state.pending_handle = normalize_handle(handle)


def _begin_pin_signup(
    handle: str,
    display_name: str,
    vibe: str,
    emoji: str,
    mascot: str,
    avatar_path: str,
    ig_photo: str,
    demo: dict[str, str],
    scrape: dict[str, Any],
    eligible: bool,
) -> None:
    """Shared PIN signup prompt — same surface UX for AI and gated tennis-ball members."""
    st.session_state.pending_handle = handle
    st.session_state.pending_animal = display_name
    st.session_state.pending_vibe = vibe
    st.session_state.pending_emoji = emoji
    st.session_state.pending_mascot = mascot
    st.session_state.pending_avatar = avatar_path
    st.session_state.pending_ig_photo = ig_photo
    st.session_state.auth_state = NEED_PIN_SIGNUP
    if not eligible:
        _lock_handle_session(handle)

    photo_path = animal_photo_path(mascot, avatar_path)
    if eligible:
        body = (
            f"{character_reveal(mascot or display_name, emoji)}\n\n"
            "Set a **4-digit PIN** to lock it in."
        )
    else:
        body = "Set a **4-digit PIN** to save your spot (numbers only)."
    append_assistant(
        body,
        image=photo_path if isinstance(photo_path, str) and os.path.isfile(photo_path) else None,
    )


def _sit_tight_line(at: str) -> str:
    return random.choice(
        [
            "Sit tight — thinking…",
            "Loading the vibes…",
            "Building your court pass…",
            "Looking for UFOs… back in a sec.",
            "Hold that serve — still loading.",
            "Warming up the ball machine…",
            "One moment. Counting tennis balls.",
            "Don’t bounce yet — loading.",
        ]
    )


def _apply_hk_name_prior(handle: str, demo: dict) -> None:
    if (demo.get("nationality") or "unknown") != "unknown":
        return
    fn = (demo.get("first_name") or "").lower().replace(" ", "")
    toks = set(_handle_name_tokens(handle))
    if (
        fn in _FEM_GIVEN
        or "yee" in fn
        or "manyee" in handle.lower()
        or any(t in _FEM_GIVEN or t in _CJK_SURNAMES for t in toks)
    ):
        demo["nationality"] = "Hong Kong"
        demo["evidence"] = (demo.get("evidence") or "") + "; Cantonese name prior → Hong Kong"


def _ig_scan_and_signup(handle: str) -> None:
    """Long Instagram lookup + gate + character. Call after a sit-tight message."""
    at = format_handle(handle)
    if handle not in ADMIN_HANDLES and _indown_lookup(handle).get("missing"):
        drop_unfinished_handle(handle)
        _tell_profile_missing(at)
        return

    ensure_pending_handle(handle)
    existing = get_user_by_handle(handle)

    resolved = resolve_member_profile(handle)
    scrape = resolved["scrape"]
    if scrape.get("profile_missing") and handle not in ADMIN_HANDLES:
        drop_unfinished_handle(handle)
        _tell_profile_missing(at)
        return

    card_ok = _profile_card_seen(scrape) or handle in ADMIN_HANDLES
    if not card_ok:
        if existing and existing.get("ig_photo_path") and existing.get("animal") and not existing.get("pin_hash"):
            mascot = existing.get("mascot") or existing.get("animal") or handle
            animal_raw = existing.get("animal") or mascot
            display_name = (
                mascot if not re.search(r"[A-Za-z\u4e00-\u9fff]", animal_raw or "") else animal_raw
            )
            emoji = existing.get("animal_emoji") or "🎾"
            avatar_path = existing.get("avatar_path") or ""
            ig_photo = existing.get("ig_photo_path") or ""
            st.session_state.pending_handle = handle
            st.session_state.pending_animal = display_name
            st.session_state.pending_vibe = existing.get("vibe") or ""
            st.session_state.pending_emoji = emoji
            st.session_state.pending_mascot = mascot
            st.session_state.pending_avatar = avatar_path
            st.session_state.pending_ig_photo = ig_photo
            st.session_state.auth_state = NEED_PIN_SIGNUP
            if existing.get("ai_enabled") is not None and not int(existing.get("ai_enabled") or 0):
                _lock_handle_session(handle)
            photo_path = animal_photo_path(mascot, avatar_path)
            append_assistant(
                f"Welcome back mid-signup, {at} — you’re still **{display_name}** {emoji}\n\n"
                "Set your **4-digit PIN** to finish (no IG re-scan).",
                image=photo_path if isinstance(photo_path, str) and os.path.isfile(photo_path) else None,
            )
            return
        drop_unfinished_handle(handle)
        _tell_profile_unreadable(at)
        return

    scraped_text = scrape.get("text") or f"instagram_handle:{handle}"
    ig_photo = scrape.get("ig_photo_path") or (existing or {}).get("ig_photo_path") or ""
    demo = resolved["demo"]
    _apply_hk_name_prior(handle, demo)

    eligible, gate_detail = settle_gate(handle, demo)
    if eligible:
        display_name, vibe, emoji, mascot, avatar_path = assign_animal_and_vibe(
            handle, scraped_text, scrape=scrape
        )
        ai_flag = 1
        assign_why = (scrape or {}).get("assign_why") or ""
    else:
        display_name, vibe, emoji, mascot, avatar_path = assign_club_tennis()
        ai_flag = 0
        assign_why = "Club tennis ball — the gate kept them out, so they did not get a matched animal."

    upsert_pending_user(
        handle,
        display_name,
        vibe,
        emoji,
        mascot=mascot,
        avatar_path=avatar_path,
        ig_photo_path=ig_photo,
        gender=demo.get("gender") or "",
        nationality=demo.get("nationality") or "",
        age_guess=demo.get("age_guess") or "",
        ai_enabled=ai_flag,
        gate_detail=gate_detail,
        assign_why=assign_why,
    )
    _begin_pin_signup(
        handle,
        display_name,
        vibe,
        emoji,
        mascot,
        avatar_path,
        ig_photo,
        demo,
        scrape,
        bool(eligible),
    )


def finish_pending_ig_scan() -> bool:
    """Run a deferred Instagram scan after the sit-tight bubble is on screen."""
    handle = normalize_handle(st.session_state.get("_ig_scan_handle") or "")
    if not handle:
        return False

    done = {"ok": False}
    err: dict[str, BaseException | None] = {"e": None}

    def _work() -> None:
        try:
            _ig_scan_and_signup(handle)
        except BaseException as exc:  # noqa: BLE001 — surface after wait loop
            err["e"] = exc
        finally:
            done["ok"] = True

    worker = threading.Thread(target=_work, daemon=True)
    worker.start()

    bar = st.progress(5, text="Loading… 5%")
    t0 = time.time()
    almost_lines = (
        "Almost there…",
        "Hang tight — finishing up…",
        "Nearly done…",
        "Last stretch…",
    )
    try:
        while not done["ok"]:
            elapsed = time.time() - t0
            pct = min(92, max(5, int(5 + elapsed * 2.8)))
            if elapsed >= 15:
                bar.progress(pct, text=f"{random.choice(almost_lines)} {pct}%")
            else:
                bar.progress(pct, text=f"Loading… {pct}%")
            time.sleep(1.2)
        worker.join(timeout=2)
        if err["e"] is not None:
            raise err["e"]
    finally:
        bar.empty()
        st.session_state.pop("_ig_scan_handle", None)
    return True


def handle_need_ig(text: str) -> None:
    raw = (text or "").strip()

    # Session locked after a gated assignment — no new handles, no @ reminders
    if st.session_state.get("handle_locked"):
        m_lock = re.search(r"@([A-Za-z0-9._]{2,30})", raw)
        if m_lock:
            tried = normalize_handle(m_lock.group(1))
            locked = normalize_handle(st.session_state.get("locked_handle") or "")
            if tried and tried != locked:
                if st.session_state.get("pending_handle"):
                    st.session_state.auth_state = NEED_PIN_SIGNUP
                append_assistant(
                    "You’re already in signup on this session — enter your **4-digit PIN** to continue."
                )
                return
        append_assistant(guest_tennis_story_reply(text, remind_ig=False))
        return

    # Require @ so handles always look like @cccpinky
    m = re.search(r"@([A-Za-z0-9._]{2,30})", raw)
    if not m:
        append_assistant(guest_tennis_story_reply(text, remind_ig=True))
        return

    handle = normalize_handle(m.group(1))
    at = format_handle(handle)

    if not re.match(r"^[A-Za-z0-9._]{2,30}$", handle):
        append_assistant(guest_tennis_story_reply(text, remind_ig=True))
        return

    ensure_pending_handle(handle)
    existing = get_user_by_handle(handle)

    # Returning member with PIN
    if existing and existing.get("pin_hash"):
        st.session_state.pending_handle = handle
        st.session_state.auth_state = NEED_PIN_LOGIN
        animal = existing.get("mascot") or existing.get("animal") or "player"
        emoji = existing.get("animal_emoji") or "🎾"
        photo = animal_photo_path(existing.get("mascot") or animal, existing.get("avatar_path"))
        ig_photo = existing.get("ig_photo_path") or ""
        ensure_ig_profile_photo(handle, ig_photo)
        if not user_ai_enabled(existing):
            _lock_handle_session(handle)
        append_assistant(
            f"Welcome back, {at} — **{animal}** {emoji}\n\n"
            f"Enter your **4-digit PIN** to unlock the club chat.",
            image=photo if isinstance(photo, str) and os.path.isfile(photo) else None,
        )
        return

    # Incomplete signup — resume PIN only when we already have a solid assignment
    if existing and not existing.get("pin_hash") and existing.get("animal"):
        was_gated = existing.get("ai_enabled") is not None and not int(existing.get("ai_enabled") or 0)
        g0 = (existing.get("gender") or "").strip().lower()
        a0 = (existing.get("age_guess") or "").strip().lower()
        thin_demo = (not g0 or g0 == "unknown") or (not a0 or a0 in {"unknown", "n/a", "na", "?"})
        empty_why = not (existing.get("assign_why") or "").strip()
        needs_rescan = (was_gated or thin_demo or empty_why) and not is_admin(existing)
        if not needs_rescan:
            mascot = existing.get("mascot") or existing.get("animal") or handle
            animal_raw = existing.get("animal") or mascot
            display_name = mascot if not re.search(r"[A-Za-z\u4e00-\u9fff]", animal_raw or "") else animal_raw
            emoji = existing.get("animal_emoji") or "🎾"
            avatar_path = existing.get("avatar_path") or ""
            ig_photo = existing.get("ig_photo_path") or ""
            ig_photo = ensure_ig_profile_photo(handle, ig_photo) or ig_photo
            st.session_state.pending_handle = handle
            st.session_state.pending_animal = display_name
            st.session_state.pending_vibe = existing.get("vibe") or ""
            st.session_state.pending_emoji = emoji
            st.session_state.pending_mascot = mascot
            st.session_state.pending_avatar = avatar_path
            st.session_state.pending_ig_photo = ig_photo
            st.session_state.auth_state = NEED_PIN_SIGNUP
            if was_gated:
                _lock_handle_session(handle)
            photo_path = animal_photo_path(mascot, avatar_path)
            append_assistant(
                f"Welcome back mid-signup, {at} — you’re still **{display_name}** {emoji}\n\n"
                "Set your **4-digit PIN** to finish (no IG re-scan).",
                image=photo_path if isinstance(photo_path, str) and os.path.isfile(photo_path) else None,
            )
            return

    # Brand-new or incomplete re-scan — show sit-tight first, finish on next run
    st.session_state["_ig_scan_handle"] = handle
    append_assistant(_sit_tight_line(at))


def handle_need_pin_signup(text: str) -> None:
    pin = re.sub(r"\D", "", text.strip())
    if not re.fullmatch(r"\d{4}", pin):
        append_assistant("PIN must be exactly **4 digits**. Example: `4821`")
        return

    user = finalize_signup(st.session_state.pending_handle, pin)
    if not user:
        append_assistant("Couldn’t save your account — try your PIN again.")
        return

    rewrite_last_user("****")
    st.session_state.user = user
    st.session_state.auth_state = LOGGED_IN
    animal = user.get("mascot") or user.get("animal") or "player"
    emoji = user.get("animal_emoji") or "🎾"
    if not user_ai_enabled(user):
        _lock_handle_session(user.get("ig_handle") or st.session_state.pending_handle)
        append_assistant(
            f"You’re in, **{animal}** {emoji}\n\n"
            + guest_tennis_story_reply("", remind_ig=False)
        )
        return
    invite = maybe_game_invite()
    notices = consume_admin_signup_notices() if is_admin(user) else ""
    notice_bit = f"\n\n{notices}" if notices else ""
    append_assistant(
        f"You’re in, **{animal}** {emoji}\n\n"
        "Ask about games, spots, or courts. "
        + (
            "Type `help` for admin commands."
            if is_admin(user)
            else ""
        )
        + invite
        + notice_bit
    )


def handle_need_pin_login(text: str) -> None:
    if text.strip().lower() in {"restart", "reset", "logout", "switch"}:
        if st.session_state.get("handle_locked"):
            append_assistant("Enter your **4-digit PIN** to continue.")
            return
        st.session_state.auth_state = NEED_IG
        st.session_state.pending_handle = ""
        append_assistant("Cool — what’s your Instagram handle?")
        return

    pin = re.sub(r"\D", "", text.strip())
    if not re.fullmatch(r"\d{4}", pin):
        append_assistant("That’s not a 4-digit PIN. Try again, or type `restart` to switch accounts.")
        return

    user = verify_pin(st.session_state.pending_handle, pin)
    if not user:
        append_assistant("PIN didn’t match. Try again.")
        return

    rewrite_last_user("****")
    if is_admin(user):
        complete_admin_login(user)
        return
    st.session_state.user = user
    st.session_state.auth_state = LOGGED_IN
    animal = user.get("mascot") or user.get("animal") or "player"
    emoji = user.get("animal_emoji") or "🎾"
    if not user_ai_enabled(user):
        _lock_handle_session(user.get("ig_handle") or "")
        append_assistant(
            f"Back on court, **{animal}** {emoji}\n\n"
            + guest_tennis_story_reply("", remind_ig=False)
        )
        return
    invite = maybe_game_invite()
    append_assistant(
        f"Back on court, **{animal}** {emoji}\n\n"
        "What do you want to know about upcoming games?"
        + invite
    )


def complete_admin_login(user: dict, welcome: str = "Back on court") -> None:
    st.session_state.user = user
    st.session_state.auth_state = LOGGED_IN
    st.session_state.pending_handle = normalize_handle(user.get("ig_handle") or "")
    st.session_state.handle_locked = False
    st.session_state.locked_handle = ""
    # Refresh from DB so seeded character (e.g. Court Shiba) shows immediately
    fresh = get_user_by_handle(user.get("ig_handle") or "") or user
    st.session_state.user = fresh
    animal = fresh.get("mascot") or fresh.get("animal") or "player"
    emoji = fresh.get("animal_emoji") or "🎾"
    invite = maybe_game_invite() if user_ai_enabled(fresh) else ""
    notices = consume_admin_signup_notices() if is_admin(fresh) else ""
    notice_bit = f"\n\n{notices}" if notices else ""
    notice_bit += persistence_warning_for_admin() if is_admin(fresh) else ""
    photo = animal_photo_path(animal, fresh.get("avatar_path"))
    photo_path = photo if isinstance(photo, str) and os.path.isfile(photo) else None
    if not user_ai_enabled(fresh):
        append_assistant(
            f"{welcome}, **{animal}** {emoji}\n\n"
            + guest_tennis_story_reply("", remind_ig=False)
            + notice_bit,
            image=photo_path,
        )
        return
    append_assistant(
        f"{welcome}, **{animal}** {emoji}\n\n"
        "Type `help` for admin commands."
        + invite
        + notice_bit,
        image=photo_path,
    )


def handle_logged_in(text: str) -> None:
    user = st.session_state.user
    lower = text.strip().lower()

    if lower in {"logout", "log out", "restart"}:
        if st.session_state.get("handle_locked") and not user_ai_enabled(user):
            append_assistant(guest_tennis_story_reply(text, remind_ig=False))
            return
        st.session_state.auth_state = NEED_IG
        st.session_state.user = None
        st.session_state.pending_handle = ""
        st.session_state.handle_locked = False
        st.session_state.locked_handle = ""
        append_assistant("Logged out. Drop an IG handle when you’re ready.")
        return

    # Admin commands: help, games, gate in/out, add game
    if is_admin(user):
        if try_admin_command(text):
            return
        parsed = parse_add_game(text)
        if parsed is not None:
            game, err = finalize_add_game(parsed)
            if err:
                append_assistant(err)
                return
            assert game is not None
            gid = insert_game(
                when_text=game["when_text"],
                location=game["location"],
                spots=game["spots"],
                notes=game.get("notes", ""),
                created_by=normalize_handle(user.get("ig_handle", "admin")),
            )
            append_assistant(
                f"Game added ✅ **#{gid}** — {game['when_text']} @ {game['location']} · "
                f"{game['spots']} spots"
            )
            return

    # Gated members: no DeepSeek — tennis stories only
    if not user_ai_enabled(user):
        append_assistant(guest_tennis_story_reply(text, remind_ig=False))
        return

    if not is_admin(user) and _confirms_game_join(text, _last_assistant_text()):
        status, game = join_next_game(user.get("ig_handle") or "")
        append_assistant(game_join_reply(status, game))
        return

    games = list_games()
    if games:
        game_rule = (
            "You may invite them to one game that is actually listed above, "
            "with its date, time, location, and spots. "
            "Do not promise to flag or notify them later."
        )
    else:
        game_rule = (
            "There are no games scheduled. If they ask, say there is no game. "
            "Do not offer to flag, notify, or watch for a future post."
        )
    extra = (
        f"Member: @{user.get('ig_handle')} · mascot {user.get('animal')}.\n"
        f"{games_as_context()}\n"
        f"{game_rule}\n"
        "Trust only the live Scheduled games block above for what exists. "
        "Never invent games, signups, or members from earlier chat messages."
    )
    if is_admin(user):
        extra += (
            "\nThis sender is a club admin. Never say you lack admin access. "
            "For member lists, signups, gates, or PIN resets, tell them to type "
            "`help` for the exact admin commands (e.g. `list users`, `signups`, "
            "`user @handle`)."
        )
    history: list[dict[str, str]] = []
    for msg in st.session_state.messages[-10:]:
        if msg["role"] in ("user", "assistant"):
            history.append({"role": msg["role"], "content": msg["content"]})
    history.append({"role": "user", "content": text})

    with st.spinner("Thinking…"):
        reply = deepseek_chat(history, extra_system=extra)
    append_assistant(reply + maybe_game_invite(reply))


def process_user_input(text: str) -> None:
    text = (text or "").strip()
    if not text:
        return

    state = st.session_state.auth_state
    avatar = user_avatar() if state == LOGGED_IN else "👤"

    # Admin one-line login: @vip 0413
    if state in {NEED_IG, NEED_PIN_LOGIN, NEED_PIN_SIGNUP}:
        quick = parse_admin_quick_login(text)
        if quick:
            handle, pin = quick
            user = verify_pin(handle, pin)
            if user:
                append_user(f"@{handle} ****", avatar=user_avatar(user))
                complete_admin_login(user)
                return
            append_user(text, avatar=avatar)
            append_assistant("PIN didn’t match. Try again, or send just your @handle.")
            return

    append_user(text, avatar=avatar)

    if state == NEED_IG:
        handle_need_ig(text)
    elif state == NEED_PIN_SIGNUP:
        handle_need_pin_signup(text)
    elif state == NEED_PIN_LOGIN:
        handle_need_pin_login(text)
    elif state == LOGGED_IN:
        handle_logged_in(text)
    else:
        st.session_state.auth_state = NEED_IG
        append_assistant("Let’s start over — what’s your IG handle?")


def placeholder_for_state() -> str:
    state = st.session_state.auth_state
    if st.session_state.get("handle_locked") and state == NEED_IG:
        return "Message…"
    return {
        NEED_IG: "@your_instagram_handle…",
        NEED_PIN_SIGNUP: "Choose a 4-digit PIN…",
        NEED_PIN_LOGIN: "Your 4-digit PIN…",
        LOGGED_IN: (
            "help"
            if is_admin(st.session_state.user)
            else (
                "Say hi…"
                if st.session_state.user and not user_ai_enabled(st.session_state.user)
                else "Any games this weekend?"
            )
        ),
    }.get(state, "Message…")


def main() -> None:
    st.set_page_config(
        page_title="playplaytennis",
        page_icon="🎾",
        layout="centered",
        menu_items={"Get help": None, "Report a bug": None, "About": None},
    )
    init_db()
    ensure_session()
    inject_styles()
    render_little_tennis_header()

    if not os.environ.get("DEEPSEEK_API_KEY"):
        try:
            has_secret = bool(st.secrets.get("DEEPSEEK_API_KEY"))
        except Exception:
            has_secret = False
        if not has_secret:
            st.warning(
                "Set `DEEPSEEK_API_KEY` in a `.env` file or Streamlit secrets "
                "before chatting. Do not hardcode the key in `app.py`."
            )

    bootstrap_greeting()
    render_messages()

    if finish_pending_ig_scan():
        st.rerun()

    prompt = st.chat_input(placeholder_for_state())
    if prompt:
        process_user_input(prompt)
        st.rerun()

    # After every run (including post-send rerun), put caret back in the input
    focus_chat_input()


if __name__ == "__main__":
    main()
