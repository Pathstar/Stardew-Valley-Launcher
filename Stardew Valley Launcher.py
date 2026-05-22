from __future__ import annotations

import threading
import traceback

import av
import numpy as np

print("start")

import json
import logging
import os
import platform
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import webbrowser
import zipfile
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, date
from pathlib import Path
from typing import List, Optional, Dict, Deque
from urllib.parse import urlparse

import json5
import requests
from PySide6 import QtCore, QtGui, QtWidgets, QtMultimedia
from pydantic import BaseModel, Field

import cloudscraper
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import base64
from apscheduler.schedulers.background import BackgroundScheduler
# pyinstaller --onedir --noconsole --icon=icon.ico version8_sp_5.py

print("import OK")

if getattr(sys, 'frozen', False):
    BASE_DIR = Path(sys.executable).resolve().parent
else:
    BASE_DIR = Path(__file__).resolve().parent

RESOURCES_PATH = BASE_DIR / "resources"
IMAGES_PATH = RESOURCES_PATH / "images"
SOUNDS_PATH = RESOURCES_PATH / "sounds"
B_EVENT_PATH = RESOURCES_PATH / ".1"

TRIGGERED_FILE_PATH = B_EVENT_PATH / "triggered"

# ------------------------------------------
from solar_lunar2date import parse_to_date

mov = None

datetime_now = datetime.now()
# datetime_now = datetime(2027, 5, 9)
# datetime_now = datetime(2026, 5, 19)
# datetime_now = datetime(2026, 5, 17)

datetime_today = datetime_now.date()
IS_MY_BIRTHDAY = (datetime_now.month == 5 and datetime_now.day == 17)

task_schd = BackgroundScheduler(timezone="Asia/Shanghai")
task_schd.start()


def count_hours(d: datetime | date) -> int | float:
    d = datetime.combine(d, datetime.min.time()) if isinstance(d, date) else d
    print(f"[count_hours] {d} - {datetime_now}")
    delta_seconds = (d - datetime_now).total_seconds()

    hours = delta_seconds / 3600

    if hours < 0:
        return hours  # 直接返回负数
    elif hours >= 1:
        return int(hours)  # 向下取整为整数
    else:
        return int(hours * 10) / 10.0  # 保留一位小数并向下取整


class BEvent:
    def __init__(self):
        try:
            trigger_file_path = B_EVENT_PATH / "trigger"
            raw = trigger_file_path.read_text(encoding="utf-8").strip()
            if raw.startswith("L"):
                self.is_lunar = True
                date_raw = raw[1:]
                year_now = datetime_now.year
                years = [year_now - 1, year_now, year_now + 1]
                maybe_dates: list[date] = [parse_to_date(f"L{y}-{date_raw}") for y in years]
                self.date = [d for d in maybe_dates if isinstance(d, date) and d >= datetime_today][0]
            else:
                self.is_lunar = False
                self.date = parse_to_date(f"{datetime_today.year}-{raw}")
        except Exception as e:
            print(e)
            self.is_lunar = False
            self.date = date(1000, 1, 1)

        self.datetime = datetime.combine(self.date, datetime.min.time())
        self.is_today = self.date == datetime_today
        self.is_2026 = self.is_today and self.date.year == 2026
        self.is_triggered = self.is_today and TRIGGERED_FILE_PATH.exists()


b_event = BEvent()
# print(b_event.is_today, b_event.is_2026)
# print(b_event.date)
# exit()
# ------------------------------------------

PRESET_STR = "预设: "

SECRET_KEY = "NOMATTERWHAT"


def is_preset(s: str) -> bool:
    return s.startswith(PRESET_STR)


PRESET_BACKGROUNDS_PATHS: dict[str, Path] = {
    "玛尼合照": IMAGES_PATH / "Marnie_photo.jpg",
    "上古水果": IMAGES_PATH / "Ancient_Fruit.png",
    "苹果": IMAGES_PATH / "Apple.jpg",
    "花束": IMAGES_PATH / "Bouquet.jpg",
    "祝尼魔（绿色）": IMAGES_PATH / "Junimo_green.jpg",
    "祝尼魔（礼物）": IMAGES_PATH / "Junimo_with_gift.jpg",
    "祝尼魔（黄色）": IMAGES_PATH / "Junimo_yellow.jpg",
    "幸运午餐": IMAGES_PATH / "Lucky Lunch.jpg",
    "甜瓜": IMAGES_PATH / "Melon.png",
    "美人鱼吊坠": IMAGES_PATH / "Mermaid's_Pendant.jpg",
    "老鼠": IMAGES_PATH / "Mouse.jpg",
    "五彩碎片": IMAGES_PATH / "Prismatic_Shard.jpg",
    "五彩碎片（带背景）": IMAGES_PATH / "Prismatic_Shard_background.jpg",
    "星露谷小鸡": IMAGES_PATH / "Stardew_Chicken.jpg",
    "星之果茶": IMAGES_PATH / "Stardrop Tea.png",
    "星之果实": IMAGES_PATH / "Stardrop.jpg",
    "结婚戒指": IMAGES_PATH / "Wedding_Ring.jpg",
    "无": None
}

PRESETS = [f"{PRESET_STR}{p}" for p in PRESET_BACKGROUNDS_PATHS.keys()]


class AudioPool(QtCore.QObject):
    """
    现代且高效的音频池，专为高频触发的音效设计。
    通过轮询机制重用 QSoundEffect 实例，严格控制最大并发数，避免音量叠加导致的爆音。
    .wav
    """

    def __init__(self, file_path: str | Path, pool_size: int = 4, parent: QtCore.QObject | None = None):
        super().__init__(parent)
        self._pool: list[QtMultimedia.QSoundEffect] = []
        self._current_index: int = 0

        # 使用 pathlib 进行现代且跨平台的路径解析
        resolved_path = Path(file_path).resolve()
        if not resolved_path.exists():
            raise FileNotFoundError(f"Audio file not found: {resolved_path}")

        url = QtCore.QUrl.fromLocalFile(str(resolved_path))

        # 预先实例化并加载音频到内存池
        for _ in range(pool_size):
            effect = QtMultimedia.QSoundEffect(self)
            effect.setSource(url)
            # 默认音量可以根据需求调整 (0.0 到 1.0)
            effect.setVolume(1.0)
            self._pool.append(effect)

    def play(self) -> None:
        """
        触发播放。采用轮询（Round-Robin）策略。
        若池中该实例正在播放，则强制打断并重启，保证每次点击都有即时反馈，同时限制了最大重叠数。
        """
        if not self._pool:
            return

        effect = self._pool[self._current_index]

        # 如果最旧的实例还在播放，先停止它以干净地重启
        if effect.isPlaying():
            effect.stop()

        effect.play()

        # 游标步进，指向下一个实例
        self._current_index = (self._current_index + 1) % len(self._pool)

    def set_volume(self, volume: float) -> None:
        """统一设置池内所有音频实例的音量 (0.0 - 1.0)"""
        valid_volume = max(0.0, min(1.0, volume))
        for effect in self._pool:
            effect.setVolume(valid_volume)




# tnt_sound = AudioPool(SOUNDS_PATH / "minecraft-explode1.mp3")


def get_preset_name(s: str):
    if not s.startswith(PRESET_STR):
        return s
    return s[len(PRESET_STR):]


# -------------------------
# Logging
# -------------------------
logging.basicConfig(level=logging.DEBUG, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
logger = logging.getLogger("stardew_launcher")

# -------------------------
# Configuration (pydantic)
# -------------------------
ICON_SOURCE_NONE = "none"
ICON_SOURCE_VERSION = "version"
ICON_SOURCE_CUSTOM = "custom"


class SaveMetadata(BaseModel):
    version_id: str = Field("", description="绑定的版本ID")
    note: str = Field("", description="自定义备注信息")
    icon_path: str = Field("", description="存档图标路径")
    icon_source: str = Field(ICON_SOURCE_NONE, description="图标来源：none / version / custom")
    icon_version_id: str = Field("", description="当图标来自绑定版本时，记录来源版本ID")


class LauncherConfig(BaseModel):
    last_version_id: Optional[str] = Field(None, description="Unique ID of last launched version")
    window_geometry: Optional[dict] = Field(default_factory=dict, description="Stores window geometry and state")
    background_path: Optional[str] = Field(None, description="Path to background image or gif")
    theme: str = Field("light", description="Theme name; reserved for future use")
    saves: Dict[str, SaveMetadata] = Field(default_factory=dict, description="存档的元数据信息 (版本绑定与备注)")
    game_root: Optional[str] = Field(None, description="Game root path selected by user or auto-detected")

    bg_history: List[str] = Field(default_factory=list, description="背景图片历史记录")
    icon_history: List[str] = Field(default_factory=list, description="图标历史记录")
    mod_notes: Dict[str, str] = Field(default_factory=dict, description="Mod的备注信息，key为Mod路径或ID")

    encrypt_nexus_api_key: Optional[str] = Field("", description="Nexus API Key")


CONFIG_FILENAME = "launcher_config.json"


def load_config(config_path: Path) -> LauncherConfig:
    if config_path.exists():
        try:
            raw = config_path.read_text(encoding="utf-8")
            return LauncherConfig.model_validate_json(raw)
        except Exception as e:
            logger.exception("Failed to load config, using defaults: %s", e)
            return LauncherConfig()
    else:
        pass
        # if datetime.now().date() in {date(2026, 5, 13), date(2026, 5, 14)}:
        #     b_video_create()
    return LauncherConfig()


def save_config(config: LauncherConfig, config_path: Path, is_sync: bool = False, indent: Optional[int] = 4) -> None:
    tmp_path = Path(str(config_path) + ".tmp")
    try:
        tmp_path.parent.mkdir(parents=True, exist_ok=True)
        json_text = config.model_dump_json(indent=indent, ensure_ascii=False)
        with open(tmp_path, "w", encoding="utf-8") as f:
            f.write(json_text)
            f.flush()
            if is_sync:
                try:
                    os.fsync(f.fileno())
                except OSError:
                    logger.exception("fsync failed for %s", tmp_path)
        os.replace(tmp_path, config_path)
    except Exception:
        logger.exception("Failed to save config to %s", config_path)
        try:
            if tmp_path.exists():
                tmp_path.unlink()
        except Exception:
            logger.debug("Failed to remove temp file %s", tmp_path)


# -------------------------
# Domain Models
# -------------------------

@dataclass
class GameVersion:
    id: str
    name: str
    base_dir: Path
    exe_path: Path
    is_modpack: bool = False
    modpack_dir: Optional[Path] = None
    note: str = ""
    icon_path: str = ""

    @property
    def mods_dir(self) -> Path:
        if self.is_modpack and self.modpack_dir:
            mods_sub = self.modpack_dir / "Mods"
            return mods_sub if mods_sub.exists() else self.modpack_dir
        return self.base_dir / "Mods"

    def save_modpack_meta(self):
        if not self.is_modpack or not self.modpack_dir:
            meta_path = self.base_dir / "modpack.json"
        else:
            meta_path = self.modpack_dir / "modpack.json"
        data = {"name": self.name, "note": self.note, "icon_path": self.icon_path}
        try:
            meta_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as e:
            logger.error(f"Failed to save modpack meta: {e}")


@dataclass
class ModInfo:
    path: Path
    is_category: bool = False
    name: str = ""
    author: str = ""
    version: str = ""
    description: str = ""
    unique_id: str = ""
    is_enabled: bool = True
    nexus_id: Optional[str] = ""
    children: List[ModInfo] = field(default_factory=list)
    note: str = ""
    has_update: bool = False
    new_version: str = ""

    _search_blob: str = None

    def matches_search(self, search_text: str) -> bool:
        if not search_text:
            return True
        search = search_text.lower()
        if self._search_blob is None:
            self._search_blob = " ".join((
                self.name,
                self.author,
                self.description,
                self.unique_id,
                self.nexus_id or "",
                str(self.path),
                self.note
            )).lower()
        return search in self._search_blob

    def __hash__(self):
        return hash(self.path)


# -------------------------
# Utilities
# -------------------------

def encrypt_api_key(api_key: str) -> str:
    if not api_key: return ""
    try:
        encoded = []
        for i, char in enumerate(api_key):
            key_c = SECRET_KEY[i % len(SECRET_KEY)]
            encoded.append(chr(ord(char) ^ ord(key_c)))
        return base64.b64encode("".join(encoded).encode('utf-8')).decode('utf-8')
    except Exception as e:
        logger.error(f"Failed to encrypt API key: {e}")
        return ""


def decrypt_api_key(encrypted_key: str) -> str:
    if not encrypted_key: return ""
    try:
        decoded_chars = base64.b64decode(encrypted_key.encode('utf-8')).decode('utf-8')
        decoded = []
        for i, char in enumerate(decoded_chars):
            key_c = SECRET_KEY[i % len(SECRET_KEY)]
            decoded.append(chr(ord(char) ^ ord(key_c)))
        return "".join(decoded)
    except Exception as e:
        logger.error(f"Failed to decrypt API key: {e}")
        return ""


def is_windows_exe(path: Path) -> bool:
    return path.is_file() and path.suffix.lower() == ".exe"


def get_program_path() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve()
    return Path(__file__).resolve()


def _normalize_root(path_like) -> Optional[Path]:
    if not path_like:
        return None
    try:
        p = Path(path_like).expanduser().resolve()
        return p if p.exists() else None
    except Exception:
        return None


def write_json_file(path: Path, data: dict, indent: int = 2) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_name(path.name + ".tmp")
    tmp_path.write_text(json.dumps(data, ensure_ascii=False, indent=indent), encoding="utf-8")
    os.replace(tmp_path, path)


def _iter_steam_roots() -> List[Path]:
    roots: List[Path] = []
    seen: set[Path] = set()

    def add(p):
        norm = _normalize_root(p)
        if norm and norm not in seen:
            seen.add(norm)
            roots.append(norm)

    if platform.system() == "Windows":
        add(Path(os.environ["PROGRAMFILES(X86)"]) / "Steam" if os.environ.get("PROGRAMFILES(X86)") else None)
        add(Path(os.environ["PROGRAMFILES"]) / "Steam" if os.environ.get("PROGRAMFILES") else None)
        add(Path.home() / "AppData" / "Local" / "Steam")
    elif platform.system() == "Darwin":
        add(Path.home() / "Library" / "Application Support" / "Steam")
    else:
        add(Path.home() / ".local" / "share" / "Steam")
        add(Path.home() / ".steam" / "steam")
        add(Path.home() / ".steam" / "root")

    return roots


def _steam_library_paths_from_vdf(steam_root: Path) -> List[Path]:
    vdf_path = steam_root / "steamapps" / "libraryfolders.vdf"
    if not vdf_path.exists():
        return []

    try:
        raw = vdf_path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return []

    paths: List[Path] = []
    seen: set[Path] = set()
    for match in re.finditer(r'"path"\s*"([^"]+)"', raw, flags=re.IGNORECASE):
        candidate = match.group(1).replace('\\\\', '\\')
        p = _normalize_root(candidate)
        if p and p not in seen:
            seen.add(p)
            paths.append(p)
    return paths


def _iter_steam_common_dirs() -> List[Path]:
    common_dirs: List[Path] = []
    seen: set[Path] = set()
    for steam_root in _iter_steam_roots():
        for library_root in [steam_root] + _steam_library_paths_from_vdf(steam_root):
            common = library_root / "steamapps" / "common"
            if common.exists() and common not in seen:
                seen.add(common)
                common_dirs.append(common)
    return common_dirs


def _scan_version_count(game_root: Path) -> int:
    try:
        return len(scan_versions(game_root))
    except Exception:
        return 0


def find_game_root(config: Optional[LauncherConfig] = None) -> Optional[Path]:
    if config and getattr(config, "game_root", None):
        configured = _normalize_root(config.game_root)
        if configured:
            return configured

    base_parent = BASE_DIR.parent
    if base_parent.exists() and _scan_version_count(base_parent) > 0:
        return base_parent

    for common_dir in _iter_steam_common_dirs():
        if _scan_version_count(common_dir) > 0:
            return common_dir

    return None


def get_saves_directory() -> Path:
    if platform.system() == "Windows":
        return Path.home() / "AppData" / "Roaming" / "StardewValley" / "Saves"
    else:
        return Path.home() / ".config" / "StardewValley" / "Saves"


def get_launcher_directory() -> Path:
    launcher_dir = get_saves_directory().parent / ".launcher"
    launcher_dir.mkdir(parents=True, exist_ok=True)
    return launcher_dir


def update_launch_record() -> dict:
    record_path = get_launcher_directory() / "path.json"
    current = {"path": str(get_program_path()), "count": 0}
    if record_path.exists():
        try:
            loaded = json.loads(record_path.read_text(encoding="utf-8"))
            if isinstance(loaded, dict):
                current.update({k: loaded.get(k, current.get(k)) for k in ("path", "count")})
        except Exception:
            pass
    try:
        current["count"] = int(current.get("count") or 0) + 1
    except Exception:
        current["count"] = 1
    current["path"] = str(get_program_path())
    write_json_file(record_path, current, indent=2)
    return current


def get_backup_directory() -> Path:
    backup_dir = get_saves_directory().parent / "backup"
    backup_dir.mkdir(parents=True, exist_ok=True)
    return backup_dir


def backup_save_folder(save_name: str) -> Optional[Path]:
    source_path = get_saves_directory() / save_name
    if not source_path.exists(): return None
    backup_dir = get_backup_directory()
    timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
    target_name = f"{save_name}_{timestamp}"
    target_path = backup_dir / target_name
    try:
        archived = shutil.make_archive(str(target_path), 'zip', str(source_path))
        return Path(archived)
    except Exception as e:
        logger.exception("Backup failed: %s", e)
        return None


def _zip_directory_excluding_backup(source_dir: Path, zip_path: Path, backup_dir_name: str = ".backup") -> None:
    """
    将目录压缩为 zip，并排除目录内部的 .backup 备份文件夹自身。
    备份包内保留模组顶层目录，便于直接恢复。
    """
    if not source_dir.exists() or not source_dir.is_dir():
        raise FileNotFoundError(f"模组目录不存在: {source_dir}")

    zip_path.parent.mkdir(parents=True, exist_ok=True)
    if zip_path.exists():
        zip_path.unlink()

    backup_dir = source_dir / backup_dir_name
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
        for root, dirs, files in os.walk(source_dir):
            root_path = Path(root)

            # 彻底排除 .backup 目录，避免把历史备份再次打包进去
            dirs[:] = [d for d in dirs if (root_path / d) != backup_dir]

            for file_name in files:
                file_path = root_path / file_name
                if backup_dir in file_path.parents:
                    continue
                if file_path.resolve() == zip_path.resolve():
                    continue
                # arcname = file_path.relative_to(source_dir.parent) # 嵌套文件夹
                arc_name = file_path.relative_to(source_dir)
                zf.write(file_path, arc_name.as_posix())


def backup_mod_folder(mod_path: Path, backup_path: Path) -> Optional[Path]:
    """
    将单个 Mod 文件夹压缩备份到该 Mod 文件夹下的 .backup 目录中，
    文件名后缀追加年月日时分秒，格式：ModName_YYYYmmddHHMMSS.zip
    """
    if not mod_path.exists() or not mod_path.is_dir():
        return None

    backup_dir = backup_path / ".backup"
    backup_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
    zip_path = backup_dir / f"{mod_path.name}_{timestamp}.zip"

    try:
        _zip_directory_excluding_backup(mod_path, zip_path)
        return zip_path
    except Exception as e:
        logger.exception("Failed to backup mod folder %s: %s", mod_path, e)
        try:
            if zip_path.exists():
                zip_path.unlink()
        except Exception:
            pass
        return None


# >>> 新增：统一把版本 ID 转成可展示的版本名
def resolve_version_display_name(version_id: str, versions: List[GameVersion]) -> str:
    if not version_id:
        return "未绑定版本"
    hit = next((v.name for v in versions if v.id == version_id), None)
    return hit or version_id


def resolve_version_icon_path(version_id: str, versions: List[GameVersion]) -> str:
    """根据版本 ID 找到该版本当前的图标路径。"""
    if not version_id:
        return ""
    hit = next((v for v in versions if v.id == version_id), None)
    return hit.icon_path if hit and hit.icon_path else ""


# >>> 新增：用于 Mod 配置合并，new_config 作为底稿，old_config 覆盖已有值
def deep_merge_dict(base: dict, override: dict) -> dict:
    merged = dict(base)
    for key, value in override.items():
        if (
                key in merged
                and isinstance(merged[key], dict)
                and isinstance(value, dict)
        ):
            merged[key] = deep_merge_dict(merged[key], value)
        else:
            merged[key] = value
    return merged


def is_newer_version(current: str, new: str) -> bool:
    def to_int_list(v: str):
        cleaned = "".join(ch for ch in v if ch.isdigit() or ch == ".")
        return [int(x) for x in cleaned.split(".") if x]

    cur_parts = to_int_list(current)
    new_parts = to_int_list(new)

    max_len = max(len(cur_parts), len(new_parts))
    cur_parts += [0] * (max_len - len(cur_parts))
    new_parts += [0] * (max_len - len(new_parts))

    return new_parts > cur_parts


def scan_versions(game_root: Path) -> List[GameVersion]:
    versions: List[GameVersion] = []
    if not game_root.exists(): return versions

    try:
        for child in game_root.iterdir():
            if not child.is_dir(): continue

            exe = child / "Stardew Valley.exe"
            smapi = child / "StardewModdingAPI.exe"
            launch_exe = smapi if smapi.exists() else exe

            def make_default_modpack(path: Path):
                default_data = {"name": pack_name, "note": note, "icon_path": icon_path}
                try:
                    path.write_text(json.dumps(default_data, ensure_ascii=False, indent=2),
                                            encoding="utf-8")
                except:
                    pass

            if not is_windows_exe(exe):
                continue

            def iter_with_parent(_child: Path):
                yield _child
                yield from _child.iterdir()

            for sub in iter_with_parent(child):
                if not sub.is_dir(): continue
                is_vanilla = sub is child

                modpack_meta = sub / "modpack.json"
                # print(str(modpack_meta))
                is_should_has_meta = is_vanilla or sub.name.lower().startswith("mod") or modpack_meta.exists()

                if not is_should_has_meta:
                    continue

                pack_name = f"{child.name} - {sub.name}"
                note = ""
                icon_path = ""

                if not modpack_meta.exists():
                    make_default_modpack(modpack_meta)
                else:
                    try:
                        meta_data = json.loads(modpack_meta.read_text(encoding="utf-8"))
                        pack_name = meta_data.get("name", pack_name)
                        note = meta_data.get("note", "")
                        icon_path = meta_data.get("icon_path", "")
                    except:
                        pass
                if is_vanilla:
                    versions.append(GameVersion(
                        id=str(child), name=child.name, base_dir=child, exe_path=launch_exe, is_modpack=False,
                        note=note, icon_path=icon_path
                    ))
                else:
                    versions.append(GameVersion(
                        id=str(sub), name=pack_name, base_dir=child, exe_path=launch_exe,
                        is_modpack=True, modpack_dir=sub, note=note, icon_path=icon_path
                    ))
    except Exception:
        logger.exception("Error scanning versions in %s", game_root)

    versions.sort(key=lambda v: v.name.lower())
    return versions


def scan_saves() -> List[Path]:
    saves = []
    saves_dir = get_saves_directory()
    if saves_dir.exists():
        try:
            for child in saves_dir.iterdir():
                if child.is_dir(): saves.append(child)
        except:
            pass
    return sorted(saves, key=lambda p: p.name.lower())


def open_in_file_explorer(path: Path) -> None:
    if not path.exists(): return
    try:
        if platform.system() == "Windows":
            subprocess.Popen(["explorer", str(path)])
        elif platform.system() == "Darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
    except:
        pass


# def launch_executable(version: GameVersion) -> Optional[subprocess.Popen]:
#     if not version.exe_path.exists():
#         return None
#
#     if version.exe_path.name == "StardewModdingAPI.exe":
#         if version.is_modpack and version.modpack_dir:
#             mods_dir = version.mods_dir
#         else:
#             mods_dir = version.base_dir / ".EmptyMods"
#             mods_dir.mkdir(exist_ok=True)
#         cmd = [str(version.exe_path), "--mods-path", str(mods_dir)]
#         exe_dir = version.base_dir
#
#     else:
#         vanilla_exe = version.base_dir / "Stardew Valley.exe"
#         if not vanilla_exe.exists():
#             return None
#         cmd = [str(vanilla_exe)]
#         exe_dir = version.base_dir
#
#     return subprocess.Popen(cmd, cwd=str(exe_dir), creationflags=subprocess.CREATE_NEW_CONSOLE)


def launch_executable(version: GameVersion) -> Optional[subprocess.Popen]:
    if not version.exe_path.exists():
        return None

    if version.is_modpack and version.modpack_dir and version.exe_path.name == "StardewModdingAPI.exe":
        cmd = [str(version.exe_path), "--mods-path", str(version.mods_dir)]
        exe_dir = version.base_dir
    else:
        vanilla_exe = version.base_dir / "Stardew Valley.exe"
        if not vanilla_exe.exists():
            return None
        cmd = [str(vanilla_exe)]
        exe_dir = version.base_dir

    return subprocess.Popen(cmd, cwd=str(exe_dir), creationflags=subprocess.CREATE_NEW_CONSOLE)


def parse_mod_directory(target_dir: Path, global_notes: Dict[str, str]) -> List[ModInfo]:
    def sort_mods(mods: List[ModInfo]) -> List[ModInfo]:
        mods.sort(key=lambda m: (not m.is_category, m.name.lower()))
        for m in mods:
            if m.is_category and m.children:
                sort_mods(m.children)
        return mods

    mods = []
    if not target_dir.exists() or not target_dir.is_dir(): return mods

    for child in target_dir.iterdir():
        if not child.is_dir(): continue
        manifest = child / "manifest.json"
        manifest_disabled = child / "manifest.json.disabled"

        if manifest.exists() or manifest_disabled.exists():
            is_enabled = manifest.exists()
            active = manifest if is_enabled else manifest_disabled
            mod_info = ModInfo(path=child, is_category=False, is_enabled=is_enabled, name=child.name)
            try:
                data = json5.loads(active.read_text(encoding="utf-8-sig"))
                mod_info.name = data.get("Name", child.name)
                mod_info.author = data.get("Author", "未知作者")
                mod_info.description = data.get("Description", "暂无描述")
                mod_info.unique_id = data.get("UniqueID", "")
                vd = data.get("Version", "无")
                if isinstance(vd, str):
                    mod_info.version = vd
                elif isinstance(vd, dict):
                    mod_info.version = f"{vd.get('MajorVersion', 1)}.{vd.get('MinorVersion', 0)}.{vd.get('PatchVersion', 0)}"
                for k in data.get("UpdateKeys", []):
                    if isinstance(k, str) and k.lower().startswith("nexus:"):
                        mod_info.nexus_id = k.split(":")[1]
                        break
            except:
                pass

            note_key = mod_info.unique_id if mod_info.unique_id else str(mod_info.path)
            mod_info.note = global_notes.get(note_key, "")

            mods.append(mod_info)
        else:
            children_mods = parse_mod_directory(child, global_notes)
            if children_mods:
                mods.append(ModInfo(path=child, is_category=True, name=child.name, children=children_mods))

    mods = sort_mods(mods)
    return mods


def apply_icon_to_label(label: QtWidgets.QLabel, icon_path: str, size: int = 64, is_modpack=False):
    """通用方法：给QLabel应用静态图或无闪烁的GIF"""
    if hasattr(label, "_current_movie"):
        label._current_movie.stop()
        del label._current_movie

    if not icon_path:
        label.clear()
        return

    if is_preset(icon_path):
        path = PRESET_BACKGROUNDS_PATHS.get(get_preset_name(icon_path))
        resolved_path = str(path) if path else ""
    else:
        resolved_path = icon_path

    if not resolved_path or not Path(resolved_path).exists():
        label.clear()
        return

    if resolved_path.lower().endswith(".gif"):
        movie = QtGui.QMovie(resolved_path)
        movie.setCacheMode(QtGui.QMovie.CacheMode.CacheAll)
        movie.setScaledSize(QtCore.QSize(size, size))
        label.setMovie(movie)
        movie.start()
        label._current_movie = movie
    else:
        img = QtGui.QPixmap(resolved_path).scaled(size, size, QtCore.Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                                  QtCore.Qt.TransformationMode.SmoothTransformation)
        label.setPixmap(img)


def map_qt_key_to_smapi(key: int) -> str:
    mapping = {
        QtCore.Qt.Key.Key_Shift: "LeftShift", QtCore.Qt.Key.Key_Control: "LeftControl",
        QtCore.Qt.Key.Key_Alt: "LeftAlt", QtCore.Qt.Key.Key_Meta: "LeftWindows",
        QtCore.Qt.Key.Key_Escape: "Escape", QtCore.Qt.Key.Key_Space: "Space",
        QtCore.Qt.Key.Key_Return: "Enter", QtCore.Qt.Key.Key_Enter: "Enter",
        QtCore.Qt.Key.Key_Backspace: "Back", QtCore.Qt.Key.Key_Tab: "Tab",
        QtCore.Qt.Key.Key_Delete: "Delete", QtCore.Qt.Key.Key_Insert: "Insert",
        QtCore.Qt.Key.Key_Home: "Home", QtCore.Qt.Key.Key_End: "End",
        QtCore.Qt.Key.Key_PageUp: "PageUp", QtCore.Qt.Key.Key_PageDown: "PageDown",
        QtCore.Qt.Key.Key_Up: "Up", QtCore.Qt.Key.Key_Down: "Down",
        QtCore.Qt.Key.Key_Left: "Left", QtCore.Qt.Key.Key_Right: "Right",
    }
    if key in mapping: return mapping[key]
    if QtCore.Qt.Key.Key_A <= key <= QtCore.Qt.Key.Key_Z: return chr(key)
    if QtCore.Qt.Key.Key_0 <= key <= QtCore.Qt.Key.Key_9: return "D" + chr(key)
    if QtCore.Qt.Key.Key_F1 <= key <= QtCore.Qt.Key.Key_F24: return "F" + str(key - QtCore.Qt.Key.Key_F1 + 1)
    char = QtGui.QKeySequence(key).toString()
    return char.upper() if char else ""


class UpdateCheckThread(QtCore.QThread):
    update_found = QtCore.Signal(str, str)  # unique_id, new_version
    finished_check = QtCore.Signal(bool)  # is_success

    def __init__(self, mods: List[ModInfo], nexus_api_key: Optional[str] = None, parent=None):
        super().__init__(parent)
        self.mods = mods
        self.nexus_api_key = nexus_api_key or ""

        # requests session with retry/backoff
        self._session = requests.Session()
        retries = Retry(total=3, backoff_factor=0.5,
                        status_forcelist=(429, 500, 502, 503, 504),
                        allowed_methods=frozenset(['GET', 'POST']))
        adapter = HTTPAdapter(max_retries=retries)
        self._session.mount("https://", adapter)
        self._session.mount("http://", adapter)
        self._session.headers.update({"User-Agent": "StardewLauncher/1.0"})

        if self.nexus_api_key:
            # Nexus API 要求 apikey header
            self._session.headers.update({"apikey": self.nexus_api_key, "Accept": "application/json"})

        # cloudscraper 用于回退抓取（绕过 Cloudflare）
        try:
            self._scraper = cloudscraper.create_scraper(browser={"custom": "StardewLauncher/1.0"})
        except Exception:
            self._scraper = None

        # 缓存已检查的 nexus_id，避免重复请求
        self._checked_ids = set()

    def _extract_numeric_id(self, nexus_id: str) -> Optional[int]:
        if not nexus_id:
            return None
        # 提取第一个连续数字序列作为 id
        m = re.search(r'(\d+)', str(nexus_id))
        if not m:
            return None
        try:
            return int(m.group(1))
        except Exception:
            return None

    def _fetch_via_api(self, mod_id: int) -> Optional[str]:
        """使用 Nexus Mods 官方 API 获取版本信息（需要 API key）"""
        url = f"https://api.nexusmods.com/v1/games/stardewvalley/mods/{mod_id}.json"
        resp = self._session.get(url, timeout=10)
        if resp.status_code == 404:
            return None
        resp.raise_for_status()
        data = resp.json()
        # API 字段可能不同，尝试常见字段
        ver = data.get("version") or data.get("latest_version") or data.get("mod_version") or ""
        if isinstance(ver, dict):
            ver = ver.get("name", "") or ""
        return (ver or "").strip()

    def _fetch_via_requests(self, mod_id: int) -> Optional[str]:
        """使用 requests 抓取页面并解析版本号（不绕过 Cloudflare）"""
        url = f"https://www.nexusmods.com/stardewvalley/mods/{mod_id}"
        resp = self._session.get(url, timeout=12)
        resp.raise_for_status()
        html = resp.text
        soup = BeautifulSoup(html, "html.parser")
        # 更稳健地查找 Version 字段
        stat_names = soup.find_all("div", class_="stat-name")
        for sn in stat_names:
            if sn.get_text(strip=True).lower() == "version":
                sv = sn.find_next_sibling("div", class_="stat-value")
                if sv:
                    return sv.get_text(strip=True)
        # 兜底正则
        m = re.search(r'<div class="stat-name">Version</div>\s*<div class="stat-value">\s*(.*?)\s*</div>', html, re.S)
        if m:
            return m.group(1).strip()
        return None

    def _fetch_via_cloudscraper(self, mod_id: int) -> Optional[str]:
        """回退方案：cloudscraper + BeautifulSoup（绕过 Cloudflare）"""
        if not self._scraper:
            return None
        url = f"https://www.nexusmods.com/stardewvalley/mods/{mod_id}"
        resp = self._scraper.get(url, timeout=15)
        resp.raise_for_status()
        html = resp.text
        soup = BeautifulSoup(html, "html.parser")
        stat_names = soup.find_all("div", class_="stat-name")
        for sn in stat_names:
            if sn.get_text(strip=True).lower() == "version":
                sv = sn.find_next_sibling("div", class_="stat-value")
                if sv:
                    return sv.get_text(strip=True)
        m = re.search(r'<div class="stat-name">Version</div>\s*<div class="stat-value">\s*(.*?)\s*</div>', html, re.S)
        if m:
            return m.group(1).strip()
        return None

    def run(self):
        any_success = False
        network_error = True
        self._checked_ids.clear()

        for mod in self.mods:
            raw_id = getattr(mod, "nexus_id", None)
            if not raw_id:
                continue

            mod_id = self._extract_numeric_id(raw_id)
            if not mod_id or mod_id <= 0:
                logger.debug(f"Invalid nexus_id for mod {getattr(mod, 'name', '<unknown>')}: {raw_id}")
                continue

            # 去重
            if mod_id in self._checked_ids:
                continue
            self._checked_ids.add(mod_id)

            try:
                new_version = None

                # 优先使用 API
                if self.nexus_api_key:
                    try:
                        new_version = self._fetch_via_api(mod_id)
                    except requests.HTTPError as e:
                        status = getattr(e.response, "status_code", None)
                        logger.debug(f"Nexus API HTTP error for {mod.name}: {e} (status={status})")
                    except Exception as e:
                        logger.debug(f"Nexus API error for {mod.name}: {e}")

                # 常规 requests
                if not new_version:
                    try:
                        new_version = self._fetch_via_requests(mod_id)
                    except Exception as e:
                        logger.debug(f"Requests fetch failed for {mod.name}: {e}")

                # cloudscraper 回退
                if not new_version and self._scraper:
                    try:
                        new_version = self._fetch_via_cloudscraper(mod_id)
                    except Exception as e:
                        logger.debug(f"Cloudscraper fetch failed for {mod.name}: {e}")

                if new_version:
                    network_error = False
                    any_success = True
                    current_ver = getattr(mod, "version", "") or ""
                    if is_newer_version(current_ver, new_version):
                        logger.info(f"Update found for {mod.name}: {current_ver} -> {new_version}")
                        self.update_found.emit(mod.unique_id, new_version)
                else:
                    logger.debug(f"No version info found for {mod.name} (id={mod_id})")
                    network_error = False

            except Exception as e:
                logger.debug(f"Failed to check update for {getattr(mod, 'name', '<unknown>')}: {e}")

            time.sleep(0.2)

        # 成功条件：至少有一个成功；失败条件：全部失败 或 完全网络错误
        success = any_success and not network_error
        self.finished_check.emit(success)


class ModUpdateThread(QtCore.QThread):
    progress = QtCore.Signal(str)
    finished_update = QtCore.Signal(int, int, int, str)

    def __init__(self, mods: List[ModInfo], nexus_api_key: str = "", parent=None):
        super().__init__(parent)
        self.mods = list(mods)
        self.nexus_api_key = nexus_api_key or ""
        self._cached_nexus_game_id: Optional[int] = None

        self._session = requests.Session()
        retries = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset(['GET', 'POST']),
        )
        adapter = HTTPAdapter(max_retries=retries)
        self._session.mount("https://", adapter)
        self._session.mount("http://", adapter)
        self._session.headers.update({"User-Agent": "StardewLauncher/1.0"})
        if self.nexus_api_key:
            self._session.headers.update({"apikey": self.nexus_api_key, "Accept": "application/json"})
        self.last_error = ''

    def _nexus_headers(self) -> dict:
        headers = {
            "User-Agent": "StardewLauncher/1.0",
            "Accept": "application/json",
        }
        if self.nexus_api_key:
            headers["apikey"] = self.nexus_api_key
        return headers

    def _extract_numeric_id(self, nexus_id: str) -> Optional[int]:
        if not nexus_id:
            return None
        m = re.search(r'(\d+)', str(nexus_id))
        if not m:
            return None
        try:
            return int(m.group(1))
        except Exception:
            return None

    def _fetch_nexus_game_id(self) -> Optional[int]:
        if self._cached_nexus_game_id is not None:
            return self._cached_nexus_game_id

        payload = {
            "query": "query game($domainName: String) { game(domainName: $domainName) { id } }",
            "variables": {"domainName": "stardewvalley"},
        }

        try:
            resp = requests.post(
                "https://api.nexusmods.com/v2/graphql",
                json=payload,
                headers=self._nexus_headers(),
                timeout=15,
            )
            resp.raise_for_status()
            data = resp.json()
            game = (data.get("data") or {}).get("game") or {}
            game_id = game.get("id")
            self._cached_nexus_game_id = int(game_id)
        except Exception as e:
            logger.debug("Failed to fetch Nexus game id: %s", e)
            self._cached_nexus_game_id = None

        return self._cached_nexus_game_id

    def _fetch_latest_nexus_file_info(self, mod_id: int, local_version: str) -> Optional[dict]:
        game_id = self._fetch_nexus_game_id()
        if not game_id:
            return None

        payload = {
            "query": (
                "query modFiles($modId: ID!, $gameId: ID!) { "
                "modFiles(modId: $modId, gameId: $gameId) { "
                "category primary uri version name date fileId } }"
            ),
            "variables": {"modId": mod_id, "gameId": game_id},
        }

        try:
            resp = requests.post(
                "https://api.nexusmods.com/v2/graphql",
                json=payload,
                headers=self._nexus_headers(),
                timeout=20,
            )
            resp.raise_for_status()
            data = resp.json()
            files = ((data.get("data") or {}).get("modFiles") or [])
        except Exception as e:
            logger.debug("Failed to fetch Nexus mod files for %s: %s", mod_id, e)
            return None

        if not files:
            return None

        def norm(v) -> str:
            return str(v or "").strip()

        def score(file_obj: dict) -> tuple:
            category = norm(file_obj.get("category")).upper()
            primary = 1 if str(file_obj.get("primary", "")).lower() in {"1", "true", "yes"} else 0
            try:
                date = int(file_obj.get("date") or 0)
            except Exception:
                date = 0
            try:
                version_newer = 1 if norm(file_obj.get("version")) and is_newer_version(local_version, norm(
                    file_obj.get("version"))) else 0
            except Exception:
                version_newer = 0
            return (version_newer, 1 if category in {"MAIN", "UPDATE"} else 0, primary, date)

        candidates = [f for f in files if norm(f.get("uri"))]
        if not candidates:
            return None

        candidates.sort(key=score, reverse=True)
        return candidates[0]

    def _get_nexus_download_url(self, mod_id: int, file_id: int) -> Optional[str]:
        url = f"https://api.nexusmods.com/v1/games/stardewvalley/mods/{mod_id}/files/{file_id}/download_link.json"
        try:
            resp = requests.get(url, headers=self._nexus_headers(), timeout=20)
            resp.raise_for_status()
            data = resp.json()
            if isinstance(data, list) and data:
                return data[0].get("URI")
        except Exception as e:
            logger.debug("Failed to get download link for mod %s file %s: %s", mod_id, file_id, e)
            self.last_error = e
        return None

    def _download_nexus_zip(self, url: str, label: str = "") -> Optional[Path]:
        url = (url or "").strip()
        if not url:
            logger.error("Nexus download url is empty: %s", label or "<unknown>")
            return None

        parsed = urlparse(url)
        if parsed.scheme not in {"http", "https"}:
            logger.error("Nexus returned non-absolute download url for %s: %r", label or "<unknown>", url)
            return None

        tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".zip")
        tmp_path = Path(tmp.name)
        tmp.close()

        try:
            with requests.get(
                    url,
                    headers=self._nexus_headers(),
                    timeout=120,
                    stream=True,
                    allow_redirects=True,
            ) as resp:
                resp.raise_for_status()
                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=1024 * 256):
                        if chunk:
                            f.write(chunk)
            return tmp_path
        except Exception as e:
            logger.exception("Failed to download Nexus zip %s: %s", label or url, e)
            try:
                if tmp_path.exists():
                    tmp_path.unlink()
            except Exception:
                pass
            return None

    @staticmethod
    def _read_json5_file(self, path: Path) -> dict:
        try:
            return json5.loads(path.read_text(encoding="utf-8-sig"))
        except Exception:
            return {}

    @staticmethod
    def _write_json_file(self, path: Path, data: dict) -> None:
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    def _update_single_zip(self, zip_path: Path, target_dir: Path) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            with zipfile.ZipFile(zip_path, 'r') as z:
                z.extractall(temp_path)

            manifest_files = list(temp_path.rglob("manifest.json")) or list(temp_path.rglob("manifest.json.disabled"))

            if not manifest_files:
                raise ValueError(f"{zip_path.name} 不是一个有效的模组，未找到 manifest")

            for manifest_file in manifest_files:
                mod_root = manifest_file.parent
                if "__MACOSX" in str(mod_root):
                    continue

                try:
                    json5.loads(manifest_file.read_text(encoding="utf-8-sig"))
                except Exception:
                    continue

                final_dest = target_dir / mod_root.name
                old_config = {}
                old_config_path = final_dest / "config.json"

                if final_dest.exists():
                    if old_config_path.exists():
                        old_config = self._read_json5_file(old_config_path)
                    shutil.rmtree(final_dest, ignore_errors=True)

                shutil.copytree(mod_root, final_dest)

                if old_config:
                    new_config_path = final_dest / "config.json"
                    if new_config_path.exists():
                        try:
                            new_config = self._read_json5_file(new_config_path)
                            merged_config = deep_merge_dict(new_config, old_config)
                            self._write_json_file(new_config_path, merged_config)
                        except Exception:
                            self._write_json_file(new_config_path, old_config)
                    else:
                        self._write_json_file(new_config_path, old_config)

    def _fetch_message_from_exception(self, e: Exception | str, timeout: float = 1.0) -> str:
        s = str(e)
        start = s.find("http")
        if start == -1:
            return ""
        end = s.find(".json", start)
        if end == -1:
            return ""
        url = s[start:end + len(".json")]
        try:
            resp = requests.get(url, timeout=timeout, headers=self._nexus_headers())
            data = resp.json()
        except Exception:
            return ""
        return data.get("message", "")

    def run(self):
        updated = 0
        skipped = 0
        failed = 0

        for mod in self.mods:
            if self.isInterruptionRequested():
                break

            mod_id = self._extract_numeric_id(getattr(mod, "nexus_id", "") or "")
            if not mod_id:
                skipped += 1
                continue

            self.progress.emit(f"正在更新：{mod.name}")

            try:
                latest_file = self._fetch_latest_nexus_file_info(mod_id, getattr(mod, "version", "") or "")
                if not latest_file:
                    skipped += 1
                    continue

                remote_version = str(latest_file.get("version") or "").strip()
                file_id = latest_file.get("fileId")
                download_url = self._get_nexus_download_url(mod_id, file_id)

                if not remote_version or not download_url:
                    skipped += 1
                    continue

                if not is_newer_version(getattr(mod, "version", "") or "", remote_version):
                    skipped += 1
                    continue

                zip_path = self._download_nexus_zip(download_url, mod.name)
                if not zip_path:
                    failed += 1
                    continue

                try:
                    self._update_single_zip(zip_path, mod.path)
                    updated += 1
                except Exception as e:
                    failed += 1
                    logger.exception("Failed to install update for %s: %s", mod.name, e)
                finally:
                    try:
                        if zip_path.exists():
                            zip_path.unlink()
                    except Exception:
                        pass

            except Exception as e:
                failed += 1
                logger.exception("Failed to update %s: %s", mod.name, e)

        error_info = self._fetch_message_from_exception(self.last_error, timeout=2.0)
        if error_info:
            error_info = f"错误信息: {error_info}"
        self.finished_update.emit(updated, skipped, failed, error_info)


# -------------------------
# UI Components
# -------------------------
class TruncatedLabel(QtWidgets.QLabel):
    def __init__(self, text="", parent=None):
        super().__init__(parent)
        self._full_text = text
        self.setSizePolicy(QtWidgets.QSizePolicy.Policy.Ignored, QtWidgets.QSizePolicy.Policy.Preferred)
        self.setMinimumWidth(20)
        if text: self.setText(text)

    def setText(self, text):
        self._full_text = text
        self._update_text()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update_text()

    def _update_text(self):
        w = self.width()
        if w <= 0: return
        fm = self.fontMetrics()
        elided = fm.elidedText(self._full_text, QtCore.Qt.TextElideMode.ElideRight, w)
        super().setText(elided)


class RemovableHistoryDelegate(QtWidgets.QStyledItemDelegate):
    X_SIZE, X_RIGHT_MARGIN = 16, 24

    def _delete_button_rect(self, rect: QtCore.QRect) -> QtCore.QRect:
        return QtCore.QRect(rect.right() - self.X_RIGHT_MARGIN, rect.top() + (rect.height() - self.X_SIZE) // 2,
                            self.X_SIZE, self.X_SIZE)

    def paint(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        super().paint(painter, option, index)
        if index.data(QtCore.Qt.ItemDataRole.UserRole):
            x_rect = self._delete_button_rect(option.rect)
            painter.save()
            painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
            painter.setPen(QtGui.QColor("#EF4444"))
            font = painter.font()
            font.setBold(True)
            painter.setFont(font)
            painter.drawText(x_rect, QtCore.Qt.AlignmentFlag.AlignCenter, "✕")
            painter.restore()

    def delete_button_rect(self, index: QtCore.QModelIndex, view: QtWidgets.QAbstractItemView) -> QtCore.QRect:
        rect = view.visualRect(index).intersected(view.viewport().rect())
        return self._delete_button_rect(rect)


class HistoryComboBox(QtWidgets.QComboBox):
    item_removed = QtCore.Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet("""
            QComboBox { padding: 6px 12px; border: 1px solid #dcdfe6; border-radius: 8px; background-color: rgba(255, 255, 255, 0.9); font-size: 14px; color: #606266; }
            QComboBox:hover { border-color: #409eff; }
            QComboBox::drop-down { subcontrol-origin: padding; subcontrol-position: top right; width: 30px; border-left: none; }
            QComboBox QAbstractItemView { background-color: rgba(255, 255, 255, 0.9); border: 1px solid #dcdfe6; border-radius: 8px; selection-background-color: #ecf5ff; selection-color: #409eff; outline: none; padding: 4px 0px; }
            QComboBox QAbstractItemView::item { min-height: 32px; padding-left: 10px; padding-right: 30px; }
            QComboBox QAbstractItemView::item:hover { background-color: #f5f7fa; color: #409eff; }
        """)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.delegate = RemovableHistoryDelegate(self)
        self.setItemDelegate(self.delegate)
        self.fixed_items_count = 0
        self.view().viewport().installEventFilter(self)
        self._pressed_delete_row: Optional[int] = None

    def _is_history_index(self, index: QtCore.QModelIndex) -> bool:
        return bool(index.isValid() and index.data(QtCore.Qt.ItemDataRole.UserRole))

    def eventFilter(self, obj, event: QtGui.QMouseEvent):
        if obj == self.view().viewport():
            et = event.type()
            if et == QtCore.QEvent.Type.MouseButtonPress:
                pos = event.position().toPoint()
                index = self.view().indexAt(pos)
                if self._is_history_index(index) and self.delegate.delete_button_rect(index, self.view()).contains(pos):
                    self._pressed_delete_row = index.row()
                    return True
                self._pressed_delete_row = None
            elif et == QtCore.QEvent.Type.MouseButtonRelease:
                pos = event.position().toPoint()
                index = self.view().indexAt(pos)
                if (self._pressed_delete_row is not None and index.isValid() and index.row() == self._pressed_delete_row
                        and self._is_history_index(index) and self.delegate.delete_button_rect(index,
                                                                                               self.view()).contains(
                            pos)):
                    text = self.itemText(index.row())
                    self.removeItem(index.row())
                    self.item_removed.emit(text)
                    self._pressed_delete_row = None
                    return True
                self._pressed_delete_row = None
            elif et in (QtCore.QEvent.Type.MouseButtonDblClick, QtCore.QEvent.Type.Leave):
                self._pressed_delete_row = None
        return super().eventFilter(obj, event)

    def add_fixed_items(self, items: List[str]):
        for item in items:
            self.addItem(item, userData=False)
            self.fixed_items_count += 1

    def load_history(self, history: List[str]):
        for item in history: self.addItem(item, userData=True)

    def push_to_top(self, text: str, is_history: bool = True):
        idx_to_remove = self.findText(text)

        # 已存在于“固定项”中，直接切回去
        if 0 <= idx_to_remove < self.fixed_items_count:
            self.setCurrentIndex(idx_to_remove)
            return

        # 已存在于历史项中，先移除
        if idx_to_remove >= self.fixed_items_count:
            self.removeItem(idx_to_remove)

        # 只有自定义项允许插入到顶部
        self.insertItem(self.fixed_items_count, text, userData=is_history)
        self.setCurrentIndex(self.fixed_items_count)


class PresetGalleryDialog(QtWidgets.QDialog):
    def __init__(self, title: str, presets: List[str], parent=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumSize(600, 450)
        self.selected_preset = None

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(16)

        header = QtWidgets.QLabel("挑选一个预设: ")
        header.setStyleSheet("font-size: 15px; font-weight: bold; color: #374151;")
        layout.addWidget(header)

        scroll = SmoothScrollArea()
        scroll.setStyleSheet("QScrollArea { border: 1px solid #E5E7EB; border-radius: 8px; background: #F9FAFB; }")

        container = QtWidgets.QWidget()
        grid = QtWidgets.QGridLayout(container)
        grid.setContentsMargins(16, 16, 16, 16)
        grid.setSpacing(12)

        # 动态生成网格，一行 4 列。修改为带图标的按钮
        col_count = 4
        for i, preset in enumerate(presets):
            btn = QtWidgets.QToolButton()
            btn.setFixedSize(120, 110)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

            display_name = get_preset_name(preset)
            path_str = PRESET_BACKGROUNDS_PATHS.get(display_name)

            if path_str and Path(path_str).exists():
                icon = QtGui.QIcon(str(path_str))
                btn.setIcon(icon)
                btn.setIconSize(QtCore.QSize(80, 80))

            btn.setText(display_name)
            btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            btn.setStyleSheet("""
                QToolButton { background: #FFFFFF; border: 2px solid #D1D5DB; border-radius: 8px; font-weight: bold; color: #4B5563; font-size: 12px; padding-bottom: 4px; }
                QToolButton:hover { border-color: #3B82F6; background: #EFF6FF; color: #1D4ED8; }
            """)
            btn.clicked.connect(lambda checked=False, p=preset: self._on_preset_clicked(p))
            grid.addWidget(btn, i // col_count, i % col_count)

        grid.setRowStretch(grid.rowCount(), 1)
        scroll.setWidget(container)
        layout.addWidget(scroll)

    def _on_preset_clicked(self, preset):
        self.selected_preset = preset
        self.accept()


class VersionPreviewCard(QtWidgets.QFrame):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("VersionPreviewCard")
        self.setStyleSheet("""
            QFrame#VersionPreviewCard { background: rgba(255,255,255,0.85); border-radius: 8px; border: 1px solid rgba(0,0,0,0.05); }
            QFrame#VersionPreviewCard:hover { background: #FFFFFF; border: 1px solid #3B82F6; }
        """)
        h = QtWidgets.QHBoxLayout(self)
        h.setContentsMargins(16, 16, 16, 16)

        self.icon_label = QtWidgets.QLabel()
        self.icon_label.setFixedSize(64, 64)
        h.addWidget(self.icon_label)

        vbox = QtWidgets.QVBoxLayout()
        title_layout = QtWidgets.QHBoxLayout()
        self.title_label = QtWidgets.QLabel()
        self.title_label.setStyleSheet("font-weight:700; font-size:16px; color:#1F2937;")
        self.tag_label = QtWidgets.QLabel()

        title_layout.addWidget(self.title_label)
        title_layout.addWidget(self.tag_label)
        title_layout.addStretch()

        self.path_label = QtWidgets.QLabel()
        self.path_label.setStyleSheet("color:#6B7280; font-size:12px;")

        vbox.addLayout(title_layout)
        vbox.addWidget(self.path_label)
        h.addLayout(vbox)
        h.addStretch()

    def update_version(self, version: Optional[GameVersion]):
        if not version:
            self.title_label.setText("未选择任何版本")
            self.tag_label.hide()
            self.path_label.setText("")
            self.icon_label.clear()
            return

        self.title_label.setText(version.name)
        self.tag_label.setText("整合包" if version.is_modpack else "原版")
        self.tag_label.setStyleSheet(
            f"font-size: 11px; padding: 2px 6px; border-radius: 4px; color: white; background: {'#8B5CF6' if version.is_modpack else '#10B981'};")
        self.tag_label.show()
        self.path_label.setText(f"路径: {version.base_dir.name}")
        apply_icon_to_label(self.icon_label, version.icon_path, 64, version.is_modpack)


class ModDetailDialog(QtWidgets.QDialog):
    note_saved = QtCore.Signal(str)

    def __init__(self, mod: ModInfo, parent=None):
        super().__init__(parent)
        self.mod = mod
        self.setWindowTitle(f"模组详情 - {mod.name}")
        self.setMinimumWidth(400)
        self.setStyleSheet("""
            QDialog { background-color: #ffffff; }
            QLabel { font-size: 13px; color: #4b5563; }
            QLineEdit, QTextEdit { border: 1px solid #D1D5DB; border-radius: 6px; padding: 6px; background-color: #F9FAFB; }
            QPushButton { border-radius: 6px; padding: 6px 16px; font-size: 13px; }
            QPushButton#save { background: #2B7BE4; color: white; font-weight: bold; }
            QPushButton#save:hover { background: #1D4ED8; }
            QPushButton#cancel { background: #f3f4f6; color: #374151; border: 1px solid #d1d5db; }
        """)
        layout = QtWidgets.QVBoxLayout(self)

        info_layout = QtWidgets.QFormLayout()

        def create_readonly_edit(text):
            le = QtWidgets.QLineEdit(text)
            le.setReadOnly(True)
            return le

        info_layout.addRow("名称:", create_readonly_edit(mod.name))
        info_layout.addRow("作者:", create_readonly_edit(mod.author))
        info_layout.addRow("版本:", create_readonly_edit(mod.version))
        info_layout.addRow("ID:", create_readonly_edit(mod.unique_id))

        desc = QtWidgets.QTextEdit(mod.description)
        desc.setReadOnly(True)
        desc.setFixedHeight(60)
        info_layout.addRow("简介:", desc)
        layout.addLayout(info_layout)

        layout.addSpacing(10)
        layout.addWidget(QtWidgets.QLabel("<b>自定义备注:</b>"))
        self.note_edit = QtWidgets.QTextEdit(mod.note)
        self.note_edit.setFixedHeight(60)
        self.note_edit.setStyleSheet("background-color: white;")
        self.note_edit.setPlaceholderText("在这里输入你对这个 Mod 的备注...")
        layout.addWidget(self.note_edit)

        btn_layout = QtWidgets.QHBoxLayout()
        btn_layout.addStretch()
        btn_cancel = QtWidgets.QPushButton("取消")
        btn_cancel.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        btn_cancel.setObjectName("cancel")
        btn_cancel.clicked.connect(self.reject)
        btn_save = QtWidgets.QPushButton("保存")
        btn_save.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        btn_save.setObjectName("save")
        btn_save.clicked.connect(self._on_save)
        btn_layout.addWidget(btn_cancel)
        btn_layout.addWidget(btn_save)
        layout.addLayout(btn_layout)

    def _on_save(self):
        new_note = self.note_edit.toPlainText().strip()
        self.note_saved.emit(new_note)
        self.accept()


# ... (KeybindFilter, ModernSwitch, ModernLineEdit, ModConfigDialog 保持原样以缩减字数) ...
class KeybindFilter(QtCore.QObject):
    mode_exited = QtCore.Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.active = False
        self.target = None
        self.current_keys = set()
        self.old_style = ""

    def start(self, widget: QtWidgets.QLineEdit):
        if self.target: self.stop()
        self.target = widget
        self.old_style = widget.styleSheet()
        widget.setStyleSheet(self.old_style + "background-color: #FEF08A; border-color: #EAB308;")
        widget.clear()
        self.current_keys.clear()
        self.active = True
        widget.installEventFilter(self)

    def eventFilter(self, obj, event):
        if not self.active or obj != self.target: return False
        if event.type() == QtCore.QEvent.Type.KeyPress:
            key = event.key()
            if key == QtCore.Qt.Key.Key_Escape:
                self.stop()
                return True
            key_str = map_qt_key_to_smapi(key)
            if key_str and key_str not in self.current_keys:
                self.current_keys.add(key_str)
                current = self.target.text()
                if current:
                    self.target.setText(current + " + " + key_str)
                else:
                    self.target.setText(key_str)
            return True
        elif event.type() == QtCore.QEvent.Type.FocusOut:
            self.stop()
            return False
        return super().eventFilter(obj, event)

    def stop(self):
        if not self.active: return
        self.active = False
        if self.target:
            self.target.removeEventFilter(self)
            self.target.setStyleSheet(self.old_style)
            self.target.clearFocus()
        self.mode_exited.emit()


class ModernSwitch(QtWidgets.QAbstractButton):
    def __init__(self, parent=None, track_radius=13, thumb_radius=10):
        super().__init__(parent)
        self.setCheckable(True)
        self.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Fixed)
        self._track_radius = track_radius
        self._thumb_radius = thumb_radius
        self._base_offset = (track_radius * 2 - thumb_radius * 2) // 2 + thumb_radius
        self._thumb_pos = float(self._base_offset)
        self.setFixedSize(track_radius * 4, track_radius * 2)
        self._anim = QtCore.QPropertyAnimation(self, b"thumb_pos", self)
        self._anim.setDuration(200)
        self._anim.setEasingCurve(QtCore.QEasingCurve.Type.InOutQuad)

    def get_thumb_pos(self): return self._thumb_pos

    def set_thumb_pos(self, pos):
        self._thumb_pos = pos
        self.update()

    thumb_pos = QtCore.Property(float, get_thumb_pos, set_thumb_pos)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._thumb_pos = self.width() - self._base_offset if self.isChecked() else self._base_offset

    def nextCheckState(self):
        super().nextCheckState()
        end = self.width() - self._base_offset if self.isChecked() else self._base_offset
        self._anim.stop()
        self._anim.setEndValue(float(end))
        self._anim.start()

    def paintEvent(self, event):
        p = QtGui.QPainter(self)
        p.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
        p.setBrush(QtGui.QColor("#3B82F6") if self.isChecked() else QtGui.QColor("#D1D5DB"))
        p.setPen(QtCore.Qt.PenStyle.NoPen)
        p.drawRoundedRect(self.rect(), self._track_radius, self._track_radius)
        p.setBrush(QtCore.Qt.GlobalColor.white)
        p.setPen(QtGui.QColor(0, 0, 0, 20))
        p.drawEllipse(QtCore.QPointF(self._thumb_pos, self.height() / 2), self._thumb_radius, self._thumb_radius)


class ModernLineEdit(QtWidgets.QLineEdit):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.setClearButtonEnabled(True)
        self._redo_shortcut = QtGui.QShortcut(QtGui.QKeySequence("Ctrl+Shift+Z"), self)
        self._redo_shortcut.activated.connect(self.redo)
        self.setStyleSheet("""
            QLineEdit { background: #F9FAFB; border: 1px solid #D1D5DB; border-radius: 6px; padding: 6px 10px; selection-background-color: #3B82F6; }
            QLineEdit:focus { border: 2px solid #3B82F6; background: #FFFFFF; }
        """)


class ModConfigDialog(QtWidgets.QDialog):
    KEY_COLUMN_WIDTH = 200
    BOOL_OFFSET = 8

    def __init__(self, config_path: Path, mod_name: str, parent=None):
        super().__init__(parent)
        self.config_path = config_path
        self.setWindowTitle(f"模组设置 - {mod_name}")
        self.setMinimumSize(500, 600)
        self.setStyleSheet(
            "QDialog { background-color: #F3F4F6; } QLabel { font-size: 13px; color: #374151; font-weight: bold; }")

        try:
            self.config_data = json5.loads(config_path.read_text(encoding='utf-8'))
        except Exception:
            self.config_data = {}

        # === PATCH START: 核心数据结构 ===
        self.field_widgets = {}  # (node_id, key) -> meta
        self.original_values = {}  # 原始值
        self.key_widgets: dict[any, QtWidgets.QLineEdit] = {}  # key label
        # === PATCH END ===

        self.keybind_filter = KeybindFilter(self)
        self._init_ui()
        QtWidgets.QApplication.instance().focusChanged.connect(self._on_focus_changed)

    def _init_ui(self):
        layout = QtWidgets.QVBoxLayout(self)

        top_bar = QtWidgets.QHBoxLayout()
        self.btn_keybind = QtWidgets.QPushButton("⌨ 键位录制")
        self.btn_keybind.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_keybind.setFocusPolicy(QtCore.Qt.FocusPolicy.NoFocus)
        self._update_btn_keybind_state(False)
        self.btn_keybind.clicked.connect(self._start_keybind_mode)
        top_bar.addWidget(self.btn_keybind)
        top_bar.addWidget(QtWidgets.QLabel("(在输入框中可启用键位录制)"))
        top_bar.addStretch()
        layout.addLayout(top_bar)

        scroll = SmoothScrollArea()
        container = QtWidgets.QWidget()
        self.form_layout = QtWidgets.QFormLayout(container)
        self.form_layout.setContentsMargins(20, 20, 20, 20)
        self.form_layout.setSpacing(16)

        if self.config_data:
            self._build_ui(self.config_data, self.form_layout)
        else:
            self.form_layout.addRow(QtWidgets.QLabel("该模组无可配置项，或文件为空。"))

        scroll.setWidget(container)
        layout.addWidget(scroll, 1)

        btn_layout = QtWidgets.QHBoxLayout()
        btn_layout.addStretch()

        btn_cancel = QtWidgets.QPushButton("取消")
        btn_cancel.setStyleSheet(
            "background: #F9FAFB; border: 1px solid #D1D5DB; color: #4B5563; border-radius: 6px; font-weight: bold;"
        )
        self.btn_save = QtWidgets.QPushButton("确定")
        self.btn_save.setStyleSheet(
            "background: #F9FAFB; border: 1px solid #D1D5DB; color: #4B5563; border-radius: 6px; font-weight: bold;"
        )

        for b in (btn_cancel, self.btn_save):
            b.setFixedSize(90, 36)
            b.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

        btn_cancel.clicked.connect(self.reject)

        self.btn_save.clicked.connect(self._on_confirm_clicked)

        btn_layout.addWidget(btn_cancel)
        btn_layout.addWidget(self.btn_save)
        layout.addLayout(btn_layout)

    # === PATCH START: 注册字段 ===
    def _register_field(self, node, key, widget, vtype):
        wid = (id(node), key)

        self.field_widgets[wid] = {
            "node": node,
            "key": key,
            "widget": widget,
            "type": vtype
        }

        self.original_values[wid] = node.get(key)

        if vtype == 'bool':
            widget.toggled.connect(lambda _, n=node, k=key: self._on_value_changed(n, k))
        else:
            widget.textChanged.connect(lambda _, n=node, k=key: self._on_value_changed(n, k))

    # === PATCH END ===

    def _build_ui(self, data_node: dict, layout: QtWidgets.QFormLayout):
        layout.setLabelAlignment(QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignTop)

        for k, v in data_node.items():
            key_lbl = QtWidgets.QLineEdit(str(k))
            key_lbl.setReadOnly(True)
            key_lbl.setAlignment(QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignVCenter)
            key_lbl.setCursorPosition(0)
            key_lbl.setFixedWidth(self.KEY_COLUMN_WIDTH)
            # === PATCH START: key 样式常量 ===
            self._key_style_normal = (
                "background: transparent; border: none; "
                "font-weight: bold; color: #4B5563; font-size: 13px;"
            )
            # === PATCH START: 强化变更态样式 ===
            self._key_style_changed = (
                "border: none; "
                "font-weight: 700; "
                "color: #D97706; "  # 更柔和橙色
                "font-size: 13px; "
                "background: rgba(245, 158, 11, 0.12); "
                "border-radius: 4px; "
                "padding-left: 4px;"
            )

            key_lbl.setStyleSheet(self._key_style_normal)

            self.key_widgets[(id(data_node), k)] = key_lbl  # === PATCH ===

            if isinstance(v, dict):
                card = QtWidgets.QFrame()
                card.setObjectName("nestedCard")
                card.setStyleSheet("""
                    QFrame#nestedCard {
                        background: #F6F7F9;
                        border: 1px solid #E5E7EB;
                        border-radius: 12px;
                    }
                """)

                card_layout = QtWidgets.QVBoxLayout(card)
                card_layout.setContentsMargins(14, 12, 14, 14)
                card_layout.setSpacing(10)

                title = QtWidgets.QLabel(str(k))
                card_layout.addWidget(title)

                inner_layout = QtWidgets.QFormLayout()
                inner_layout.setContentsMargins(0, 0, 0, 0)
                inner_layout.setSpacing(12)

                self._build_ui(v, inner_layout)
                card_layout.addLayout(inner_layout)

                layout.addRow(card)

            elif isinstance(v, bool):
                cb_container = QtWidgets.QWidget()
                cb_layout = QtWidgets.QHBoxLayout(cb_container)
                cb_layout.setContentsMargins(self.BOOL_OFFSET, 0, 0, 0)

                cb = ModernSwitch()
                cb.setChecked(v)

                cb_layout.addWidget(cb)
                cb_layout.addStretch()

                self._register_field(data_node, k, cb, 'bool')
                layout.addRow(key_lbl, cb_container)

            elif isinstance(v, (int, float)):
                le = ModernLineEdit(str(v))
                le.setValidator(QtGui.QDoubleValidator(self))
                le.setCursorPosition(0)

                self._register_field(data_node, k, le, 'int' if isinstance(v, int) else 'float')
                layout.addRow(key_lbl, le)

            else:
                le = ModernLineEdit("" if v is None else str(v))
                if v is None:
                    le.setPlaceholderText("null")
                else:
                    le.setProperty("is_string", True)

                le.setCursorPosition(0)

                self._register_field(data_node, k, le, 'null' if v is None else 'str')
                layout.addRow(key_lbl, le)

    # === PATCH START: 变更检测 ===
    def _get_widget_value(self, widget, vtype):
        if vtype == 'bool':
            return widget.isChecked()

        if hasattr(widget, 'text'):
            text = widget.text()

            if vtype == 'int':
                try:
                    return int(text)
                except:
                    return text

            if vtype == 'float':
                try:
                    return float(text)
                except:
                    return text

            if vtype == 'null':
                return None if text.strip().lower() == 'null' else text

            return text

        return None

    def _on_value_changed(self, node, key):
        wid = (id(node), key)
        info = self.field_widgets.get(wid)
        if not info:
            return

        widget = info["widget"]
        vtype = info["type"]

        current = self._get_widget_value(widget, vtype)
        original = self.original_values.get(wid)

        label = self.key_widgets.get(wid)
        if not label:
            return

        changed = current != original

        if changed:
            label.setText(f"{key} *")
            label.setStyleSheet(self._key_style_changed)
        else:
            label.setText(str(key))
            label.setStyleSheet(self._key_style_normal)
        label.setCursorPosition(0)

        self._update_save_button_state()

    # === PATCH END ===

    # === PATCH START: 按钮状态 ===
    def _update_save_button_state(self):
        has_change = False

        for wid, info in self.field_widgets.items():
            widget = info["widget"]
            vtype = info["type"]

            current = self._get_widget_value(widget, vtype)
            original = self.original_values.get(wid)

            if current != original:
                has_change = True
                break

        if has_change:
            self.btn_save.setText("💾 保存")
            self.btn_save.setStyleSheet("""
                QPushButton {
                    background: #2B7BE4;
                    color: white;
                    border: none;
                    border-radius: 6px;
                    font-weight: bold;
                }
                QPushButton:hover {
                    background: #3C88EA;  /* 悬停时稍微变亮 */
                }
            """)
        else:
            self.btn_save.setText("确定")
            self.btn_save.setStyleSheet("""
                QPushButton {
                    background: #F9FAFB;
                    border: 1px solid #D1D5DB;
                    color: #4B5563;
                    border-radius: 6px;
                    font-weight: bold;
                }
                QPushButton:hover {
                    background: #F3F4F6;  /* 悬停时稍微加深灰白 */
                }
            """)

    # === PATCH END ===

    def _on_confirm_clicked(self):
        if self.btn_save.text() == "确定":
            self.accept()
        else:
            self._save_config()

    def _update_btn_keybind_state(self, enabled: bool):
        self.btn_keybind.setEnabled(enabled)
        if enabled:
            self.btn_keybind.setStyleSheet(
                "background: #8B5CF6; color: white; border-radius: 6px; padding: 8px 12px; font-weight: bold;")
        else:
            self.btn_keybind.setStyleSheet(
                "background: #E5E7EB; color: #9CA3AF; border-radius: 6px; padding: 8px 12px; font-weight: bold;")

    def _on_focus_changed(self, old, new):
        if not self.isActiveWindow():
            return
        if isinstance(new, QtWidgets.QLineEdit) and new.property("is_string"):
            self._update_btn_keybind_state(True)
        else:
            self._update_btn_keybind_state(False)

    def _start_keybind_mode(self):
        fw = QtWidgets.QApplication.focusWidget()
        if isinstance(fw, QtWidgets.QLineEdit) and fw.property("is_string"):
            self.keybind_filter.start(fw)

    def _save_config(self):
        for wid, info in self.field_widgets.items():
            node = info["node"]
            k = info["key"]
            widget = info["widget"]
            vtype = info["type"]

            value = self._get_widget_value(widget, vtype)

            if vtype in ('int', 'float'):
                if isinstance(value, (int, float)):
                    node[k] = value
            else:
                node[k] = value

        try:
            self.config_path.write_text(
                json.dumps(self.config_data, ensure_ascii=False, indent=2),
                encoding='utf-8'
            )
            self.accept()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "错误", f"保存失败: {e}")

    def closeEvent(self, event):
        try:
            QtWidgets.QApplication.instance().focusChanged.disconnect(self._on_focus_changed)
        except:
            pass
        super().closeEvent(event)


class ClickableWidget(QtWidgets.QFrame):
    clicked = QtCore.Signal()
    settings_clicked = QtCore.Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.btn_settings = QtWidgets.QPushButton("⚙ 设置")
        self.btn_settings.setFixedSize(85, 36)
        self.btn_settings.setStyleSheet("""
            QPushButton {
                background-color: white;
                border: 1px solid #ddd;
                border-radius: 8px;
                color: #333;
                font-size: 13px;
                font-weight: 600;
            }
            QPushButton:hover {
                background-color: #f5f5f5;
                border: 1px solid #bbb;
            }
            QPushButton:pressed {
                background-color: #eaeaea;
                border: 1px solid #aaa;
            }
        """)
        self.btn_settings.hide()
        self.btn_settings.clicked.connect(self.settings_clicked.emit)

    def mouseReleaseEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton: self.clicked.emit()
        super().mouseReleaseEvent(event)

    def enterEvent(self, event):
        self.btn_settings.show()
        super().enterEvent(event)

    def leaveEvent(self, event):
        self.btn_settings.hide()
        super().leaveEvent(event)


class VersionListCard(ClickableWidget):
    def __init__(self, version: GameVersion, parent=None):
        super().__init__(parent)
        self.version = version
        self.setStyleSheet("""
            ClickableWidget { background: rgba(255,255,255,0.85); border-radius: 8px; border: 1px solid rgba(0,0,0,0.05); }
            ClickableWidget:hover { background: #FFFFFF; border: 1px solid #3B82F6; }
        """)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        h = QtWidgets.QHBoxLayout(self)
        h.setContentsMargins(16, 16, 16, 16)
        self.icon_label = QtWidgets.QLabel()
        self.icon_label.setFixedSize(64, 64)
        h.addWidget(self.icon_label)
        vbox = QtWidgets.QVBoxLayout()
        title_layout = QtWidgets.QHBoxLayout()
        self.title_label = QtWidgets.QLabel()
        self.title_label.setStyleSheet("font-weight:700; font-size:16px; color:#1F2937;")
        self.tag_label = QtWidgets.QLabel("整合包" if version.is_modpack else "原版")
        self.tag_label.setStyleSheet(
            f"font-size: 11px; padding: 2px 6px; border-radius: 4px; color: white; background: {'#8B5CF6' if version.is_modpack else '#10B981'};")
        title_layout.addWidget(self.title_label)
        title_layout.addWidget(self.tag_label)
        title_layout.addStretch()
        self.path_label = QtWidgets.QLabel(f"路径: {version.base_dir.name}")
        self.path_label.setStyleSheet("color:#6B7280; font-size:12px;")
        vbox.addLayout(title_layout)
        vbox.addWidget(self.path_label)
        h.addLayout(vbox)
        h.addStretch()
        h.addWidget(self.btn_settings)
        self.update_ui()

    def update_ui(self):
        self.title_label.setText(self.version.name)
        apply_icon_to_label(self.icon_label, self.version.icon_path, 64, self.version.is_modpack)


class SmoothScrollArea(QtWidgets.QScrollArea):
    def __init__(self, parent=None, duration: int = 180, step_pixels: int = 60):
        super().__init__(parent)
        self.duration, self.step_pixels = duration, step_pixels
        self._scroll_animation = QtCore.QPropertyAnimation(self.verticalScrollBar(), b"value", self)
        self._scroll_animation.setEasingCurve(QtCore.QEasingCurve.Type.OutCubic)
        self._target_value = self.verticalScrollBar().value()
        self.setWidgetResizable(True)
        self.setStyleSheet("""
            QScrollArea { border: none; background: transparent; }
            QScrollArea > QWidget > QWidget { background: transparent; }
            QScrollBar:vertical { border: none; background: rgba(0, 0, 0, 0.04); width: 8px; margin: 4px 2px; border-radius: 4px; }
            QScrollBar::handle:vertical { background: rgba(0, 0, 0, 0.25); min-height: 28px; border-radius: 4px; }
            QScrollBar::handle:vertical:hover { background: rgba(0, 0, 0, 0.4); }
        """)

    def wheelEvent(self, event):
        delta = event.angleDelta().y()
        if delta != 0:
            scrollbar = self.verticalScrollBar()
            start_value = self._target_value if self._scroll_animation.state() == QtCore.QAbstractAnimation.State.Running else scrollbar.value()
            target = max(scrollbar.minimum(),
                         min(scrollbar.maximum(), start_value - int((delta / 120.0) * self.step_pixels)))
            self._target_value = target
            self._scroll_animation.stop()
            self._scroll_animation.setDuration(self.duration)
            self._scroll_animation.setStartValue(scrollbar.value())
            self._scroll_animation.setEndValue(target)
            self._scroll_animation.start()
            event.accept()
        else:
            super().wheelEvent(event)


class NoWheelComboBox(QtWidgets.QComboBox):
    def wheelEvent(self, event): event.ignore()


class DeleteConfirmDialog(QtWidgets.QDialog):
    def __init__(self, title_text: str, msg_text: str, parent=None):
        super().__init__(parent)
        self.setWindowTitle("确认删除")
        self.setModal(True)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Dialog
            | QtCore.Qt.WindowType.FramelessWindowHint
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose, True)

        self.setFixedSize(420, 220)

        root = QtWidgets.QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)

        card = QtWidgets.QFrame(self)
        card.setObjectName("deleteCard")
        card.setStyleSheet("""
            QFrame#deleteCard {
                background: rgba(255, 255, 255, 0.98);
                border: 1px solid rgba(239, 68, 68, 0.14);
                border-radius: 20px;
            }
            QLabel#titleLabel {
                color: #111827;
                font-size: 18px;
                font-weight: 800;
            }
            QLabel#msgLabel {
                color: #475569;
                font-size: 13px;
                line-height: 1.6;
            }
            QPushButton {
                border: none;
                border-radius: 12px;
                padding: 10px 16px;
                font-size: 13px;
                font-weight: 700;
                min-width: 92px;
            }
        """)

        layout = QtWidgets.QVBoxLayout(card)
        layout.setContentsMargins(22, 20, 22, 20)
        layout.setSpacing(14)

        title = QtWidgets.QLabel(title_text, card)
        title.setObjectName("titleLabel")

        msg = QtWidgets.QLabel(msg_text, card)
        msg.setObjectName("msgLabel")
        msg.setWordWrap(True)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()

        cancel_btn = QtWidgets.QPushButton("取消", card)
        delete_btn = QtWidgets.QPushButton("确认删除", card)
        cancel_btn.setStyleSheet(
            "QPushButton { background: #F1F5F9; color: #334155; } QPushButton:hover { background: #E2E8F0; }")
        delete_btn.setStyleSheet(
            "QPushButton { background: #EF4444; color: white; } QPushButton:hover { background: #DC2626; }")

        cancel_btn.clicked.connect(self.reject)
        delete_btn.clicked.connect(self.accept)

        btn_row.addWidget(cancel_btn)
        btn_row.addWidget(delete_btn)

        layout.addWidget(title)
        layout.addWidget(msg)
        layout.addStretch(1)
        layout.addLayout(btn_row)
        root.addWidget(card)


class ModItemWidget(QtWidgets.QFrame):
    selection_changed = QtCore.Signal(bool, object)
    open_folder = QtCore.Signal(object)
    open_web = QtCore.Signal(object)
    show_details = QtCore.Signal(object)
    open_settings = QtCore.Signal(object)

    def __init__(self, mod: ModInfo, parent=None):
        super().__init__(parent)
        self.mod = mod
        self.selected = False
        self._should_show = True
        self._container = self
        self.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
        self.setFixedHeight(60)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self._init_ui()

    def _init_ui(self):
        self.setObjectName("modItem")
        layout = QtWidgets.QHBoxLayout(self)
        layout.setContentsMargins(12, 8, 12, 8)
        layout.setSpacing(12)

        info_layout = QtWidgets.QVBoxLayout()
        info_layout.setSpacing(0)
        top_info = QtWidgets.QHBoxLayout()

        self.name_lbl = QtWidgets.QLabel()
        self.name_lbl.setTextFormat(QtCore.Qt.TextFormat.RichText)
        self.name_lbl.setSizePolicy(QtWidgets.QSizePolicy.Policy.Ignored, QtWidgets.QSizePolicy.Policy.Preferred)
        self.name_lbl.setMinimumWidth(20)

        self.ver_lbl = QtWidgets.QLabel(f"v{self.mod.version}")
        self.ver_lbl.setStyleSheet(
            "color: #6B7280; font-size: 11px; background: rgba(0,0,0,0.05); padding: 2px 6px; border-radius: 4px;")

        top_info.addWidget(self.name_lbl, 1)
        top_info.addWidget(self.ver_lbl)
        info_layout.addLayout(top_info)

        self.author_desc = TruncatedLabel()
        self.author_desc.setStyleSheet("color: #6B7280; font-size: 12px;")
        info_layout.addWidget(self.author_desc)
        layout.addLayout(info_layout, stretch=1)

        self.action_container = QtWidgets.QWidget()
        # 去除神秘灰色竖线
        self.action_container.setStyleSheet("background: transparent; border: none;")
        action_layout = QtWidgets.QHBoxLayout(self.action_container)
        action_layout.setContentsMargins(0, 0, 0, 0)
        action_layout.setSpacing(6)

        self.btn_folder = QtWidgets.QPushButton("📁目录")
        self.btn_web = QtWidgets.QPushButton("🌐网页")
        self.btn_settings = QtWidgets.QPushButton("⚙设置")
        self.btn_details = QtWidgets.QPushButton("📄详情")

        for btn in (self.btn_folder, self.btn_web, self.btn_settings, self.btn_details):
            btn.setFixedSize(70, 36)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            btn.setStyleSheet(
                "QPushButton { background: #F3F4F6; border: 1px solid #E5E7EB; border-radius: 4px; color: #374151; font-size: 11px;} QPushButton:hover { background: #E5E7EB; }")
            action_layout.addWidget(btn)

        self.action_container.hide()
        layout.addWidget(self.action_container)

        self.btn_folder.clicked.connect(lambda: self.open_folder.emit(self))
        self.btn_web.clicked.connect(lambda: self.open_web.emit(self.mod))
        self.btn_settings.clicked.connect(lambda: self.open_settings.emit(self.mod))
        self.btn_details.clicked.connect(lambda: self.show_details.emit(self.mod))
        self._update_style()

    def _update_style(self):
        bg = "#EBF5FF" if self.selected else (
            "rgba(255, 255, 255, 0.9)" if self.mod.is_enabled else "rgba(240, 240, 240, 0.4)")
        border_color = "#3B82F6" if self.selected else "rgba(0,0,0,0.08)"
        left_border = "4px solid #3B82F6" if self.selected else "4px solid transparent"
        title_color = "#111827" if self.mod.is_enabled else "#9CA3AF"

        self.setStyleSheet(f"""
            QFrame#modItem {{ background: {bg}; border: 1px solid {border_color}; border-left: {left_border}; border-radius: 6px; }}
            QFrame#modItem:hover {{ background: {"#DBEAFE" if self.selected else "rgba(255,255,255,0.9)"}; border: 1px solid #3B82F6; border-left: 4px solid #3B82F6; }}
        """)

        base_name = f"{'🚫 ' if not self.mod.is_enabled else ''}{self.mod.name}"
        if not self.mod.is_enabled: base_name = f"<s>{base_name}</s>"
        name_text = f"<span style='font-weight: bold; font-size: 14px; color: {title_color};'>{base_name}</span>"
        if self.mod.note: name_text += f" <span style='color: #9CA3AF; font-size: 12px;'>{self.mod.note}</span>"
        self.name_lbl.setText(name_text)

        # 绿色高亮新版本
        if self.mod.has_update:
            self.ver_lbl.setText(f"v{self.mod.version} ➜ v{self.mod.new_version}")
            self.ver_lbl.setStyleSheet(
                "color: #059669; font-size: 11px; background: #D1FAE5; font-weight: bold; padding: 2px 6px; border-radius: 4px;")
        else:
            self.ver_lbl.setText(f"v{self.mod.version}")
            self.ver_lbl.setStyleSheet(
                "color: #6B7280; font-size: 11px; background: rgba(0,0,0,0.05); padding: 2px 6px; border-radius: 4px;")

        self.author_desc.setText(f"作者: {self.mod.author} | 简介: {self.mod.description}")

    def toggle_selection(self, state: Optional[bool] = None):
        self.selected = not self.selected if state is None else state
        self._update_style()
        self.selection_changed.emit(self.selected, self.mod)

    def mouseReleaseEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton and not isinstance(
                self.childAt(event.position().toPoint()), QtWidgets.QPushButton
        ):
            self.toggle_selection()
        super().mouseReleaseEvent(event)

    def enterEvent(self, event):
        self.action_container.show()
        super().enterEvent(event)

    def leaveEvent(self, event):
        self.action_container.hide()
        super().leaveEvent(event)


class ModManagerPage(QtWidgets.QWidget):
    back_requested = QtCore.Signal()
    mod_note_changed = QtCore.Signal(str, str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)
        self.current_version: Optional[GameVersion] = None
        self.global_notes = {}
        self.all_mods: List[ModInfo] = []
        self.mod_widgets: List[ModItemWidget] = []
        self.category_refs: List[tuple[QtWidgets.QFrame, List[ModItemWidget], QtWidgets.QFrame, ModInfo]] = []
        self.selected_mods: set[ModInfo] = set()
        self.current_filter = "all"
        self._all_expanded = True
        self.nexus_api_key = ""
        self.setAcceptDrops(True)  # 允许拖放
        self._update_thread = None
        self._mod_update_thread = None
        self._init_ui()

    def _init_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(12)

        top_nav = QtWidgets.QHBoxLayout()
        self.btn_back = QtWidgets.QPushButton("← 返回设置")
        self.btn_back.setFixedSize(85, 32)
        self.btn_back.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_back.setStyleSheet("""
            QPushButton {
                background-color: rgba(255, 255, 255, 0.7);
                border: 1px solid rgba(255, 255, 255, 0.6);
                border-radius: 12px;
                padding: 6px 8px;
                color: #222;
                font-weight: 500;
            }

            QPushButton:hover {
                background-color: rgba(255, 255, 255, 0.8);
            }

            QPushButton:pressed {
                background-color: rgba(255, 255, 255, 0.5);
            }
        """)
        self.btn_back.clicked.connect(self.back_requested.emit)
        self.title_label = QtWidgets.QLabel("Mod 管理")
        self.title_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.title_label.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Maximum,
            QtWidgets.QSizePolicy.Policy.Fixed
        )
        self.title_label.setFixedHeight(36)
        self.title_label.setStyleSheet("""
             QLabel {
                 background: rgba(255, 255, 255, 0.8);
                 border-radius: 12px;
                 padding: 6px 16px;
                 font-size: 15px;
                 font-weight: 600;
                 color: #374151;
                 border: 1px solid rgba(0, 0, 0, 0.06);
             }
         """)
        top_nav.addWidget(self.btn_back)
        top_nav.addSpacing(4)
        top_nav.addWidget(self.title_label)
        top_nav.addStretch()
        layout.addLayout(top_nav)

        action_panel = QtWidgets.QFrame()
        action_panel.setObjectName("actionPanel")
        action_panel.setStyleSheet("""
            QFrame#actionPanel {
                background: rgba(255,255,255,0.45);
                border: 1px solid rgba(0,0,0,0.06);
                border-radius: 16px;
            }
        """)
        action_panel_layout = QtWidgets.QVBoxLayout(action_panel)
        action_panel_layout.setContentsMargins(12, 12, 12, 12)
        action_panel_layout.setSpacing(10)

        self.search_input = QtWidgets.QLineEdit()
        self.search_input.setPlaceholderText("🔍 搜索 Mod 名称、作者或备注...")
        self.search_input.setFixedHeight(38)
        self.search_input.setStyleSheet(
            "border: 1px solid #ccc; border-radius: 18px; padding: 0 16px; background: rgba(255,255,255,0.85);")
        self.search_input.textChanged.connect(self._apply_filters)

        action_panel_layout.addWidget(self.search_input)

        # 第二行：所有按钮平均占宽
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.setSpacing(10)
        btn_row_2 = QtWidgets.QHBoxLayout()
        btn_row_2.setSpacing(10)

        self.btn_install_zip = QtWidgets.QPushButton("📦 安装Zip")
        self.btn_refresh_mod = QtWidgets.QPushButton("🌀 刷新模组")
        self.btn_check_update = QtWidgets.QPushButton("🔄 检查更新")
        self.btn_download = QtWidgets.QPushButton("🌐 下载Mod")
        self.btn_open_mods = QtWidgets.QPushButton("📁 模组文件夹")
        self.btn_toggle_fold = QtWidgets.QPushButton("↕ 全部折叠")
        self.btn_select_all = QtWidgets.QPushButton("☑ 全选可见")

        buttons = [
            self.btn_install_zip, self.btn_refresh_mod, self.btn_check_update,
            self.btn_download, self.btn_open_mods, self.btn_toggle_fold,
            self.btn_select_all
        ]

        for btn in buttons:
            btn.setFixedHeight(36)
            btn.setMinimumWidth(0)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            btn.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
            btn.setStyleSheet(
                "QPushButton { background: #ffffff; border: 1px solid #d1d5db; border-radius: 10px; padding: 0 12px; font-size: 13px; color: #374151; } QPushButton:hover { background: #f3f4f6; }")

        for i, btn in enumerate(buttons):
            if i < 4:
                btn_row.addWidget(btn, 1)
            else:
                btn_row_2.addWidget(btn, 1)

        action_panel_layout.addLayout(btn_row)
        action_panel_layout.addLayout(btn_row_2)
        layout.addWidget(action_panel)

        self.tab_group = QtWidgets.QButtonGroup(self)
        tab_layout = QtWidgets.QHBoxLayout()
        tab_layout.setSpacing(0)
        tab_layout.setContentsMargins(0, 0, 0, 0)
        self.btn_tab_all = QtWidgets.QPushButton("全部 (0)")
        self.btn_tab_enabled = QtWidgets.QPushButton("已启用 (0)")
        self.btn_tab_disabled = QtWidgets.QPushButton("已禁用 (0)")
        for i, btn in enumerate((self.btn_tab_all, self.btn_tab_enabled, self.btn_tab_disabled)):
            btn.setCheckable(True)
            btn.setFixedHeight(36)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            self.tab_group.addButton(btn, i)
            tab_layout.addWidget(btn)
        self.btn_tab_all.setChecked(True)
        self.tab_group.idToggled.connect(self._on_tab_toggled)

        tab_css = "QPushButton { background: rgba(255,255,255,0.5); border: 1px solid #d1d5db; color: #4b5563; font-weight: bold; } QPushButton:checked { background: #2B7BE4; color: white; border: 1px solid #2B7BE4; }"
        self.btn_tab_all.setStyleSheet(
            tab_css + "border-top-left-radius: 6px; border-bottom-left-radius: 6px; border-right: none;")
        self.btn_tab_enabled.setStyleSheet(tab_css + "border-radius: 0; border-right: none;")
        self.btn_tab_disabled.setStyleSheet(tab_css + "border-top-right-radius: 6px; border-bottom-right-radius: 6px;")

        tab_container = QtWidgets.QWidget()
        tab_container.setLayout(tab_layout)
        layout.addWidget(tab_container)

        self.scroll_area = SmoothScrollArea()
        self.list_container = QtWidgets.QWidget()
        self.list_layout = QtWidgets.QVBoxLayout(self.list_container)
        self.list_layout.setContentsMargins(0, 0, 0, 40)
        self.list_layout.setSpacing(8)
        self.list_layout.setAlignment(QtCore.Qt.AlignmentFlag.AlignTop)
        self.list_layout.addStretch()
        self.scroll_area.setWidget(self.list_container)
        layout.addWidget(self.scroll_area)

        self.bottom_bar = QtWidgets.QFrame(self)
        self.bottom_bar.setObjectName("bottomBar")
        self.bottom_bar.setFixedHeight(56)
        self.bottom_bar.setStyleSheet("""
            QFrame#bottomBar { background: #1F2937; border-radius: 28px; border: 1px solid #374151; }
            QLabel { color: white; font-weight: bold; font-size: 14px; margin-left: 12px; }
        """)
        bb_layout = QtWidgets.QHBoxLayout(self.bottom_bar)
        bb_layout.setContentsMargins(12, 0, 12, 0)
        self.lbl_selected_count = QtWidgets.QLabel("已选择 0 个")
        bb_layout.addWidget(self.lbl_selected_count)
        bb_layout.addStretch()

        self.btn_mass_update = QtWidgets.QPushButton("更新")
        self.btn_mass_enable = QtWidgets.QPushButton("启用")
        self.btn_mass_disable = QtWidgets.QPushButton("禁用")
        self.btn_mass_delete = QtWidgets.QPushButton("删除")
        self.btn_mass_cancel = QtWidgets.QPushButton("取消选择")
        for btn in (
                self.btn_mass_update, self.btn_mass_enable, self.btn_mass_disable, self.btn_mass_delete,
                self.btn_mass_cancel):
            btn.setFixedHeight(36)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            bb_layout.addWidget(btn)

        self.btn_mass_update.setStyleSheet(
            "background: #2B7BE4; color: white; border: none; border-radius: 18px; padding: 0 16px; font-weight: bold;")
        self.btn_mass_enable.setStyleSheet(
            "background: #10B981; color: white; border: none; border-radius: 18px; padding: 0 16px; font-weight: bold;")
        self.btn_mass_disable.setStyleSheet(
            "background: #F59E0B; color: white; border: none; border-radius: 18px; padding: 0 16px; font-weight: bold;")
        self.btn_mass_delete.setStyleSheet(
            "background: #EF4444; color: white; border: none; border-radius: 18px; padding: 0 16px; font-weight: bold;")
        self.btn_mass_cancel.setStyleSheet(
            "background: transparent; color: #9CA3AF; border: 1px solid #4B5563; border-radius: 18px; padding: 0 16px;")
        self.bottom_bar.hide()

        self.btn_install_zip.clicked.connect(self._install_zip_via_dialog)
        self.btn_refresh_mod.clicked.connect(self.reload_mods)
        self.btn_check_update.clicked.connect(self._check_mod_updates)
        self.btn_toggle_fold.clicked.connect(self._toggle_fold_all)
        self.btn_open_mods.clicked.connect(self._open_mods_folder)
        self.btn_download.clicked.connect(self._download_mods)
        self.btn_select_all.clicked.connect(self._select_all_visible)
        self.btn_mass_update.clicked.connect(self._update_selected_mods)
        self.btn_mass_enable.clicked.connect(lambda: self._mass_action("enable"))
        self.btn_mass_disable.clicked.connect(lambda: self._mass_action("disable"))
        self.btn_mass_delete.clicked.connect(lambda: self._mass_action("delete"))
        self.btn_mass_cancel.clicked.connect(self._clear_selection)

        # 动画计时器
        self._update_timer = QtCore.QTimer(self)
        self._update_timer.timeout.connect(self._animate_update_btn)
        self._spinner_frames = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
        self._spinner_idx = 0

    def dragEnterEvent(self, event: QtGui.QDragEnterEvent):
        if event.mimeData().hasUrls():
            for url in event.mimeData().urls():
                if url.toLocalFile().lower().endswith('.zip'):
                    event.acceptProposedAction()
                    return

    def dropEvent(self, event: QtGui.QDropEvent):
        urls = [url.toLocalFile() for url in event.mimeData().urls() if url.toLocalFile().lower().endswith('.zip')]
        if not urls: return

        # 判断拖入目标文件夹
        target_dir = self.current_version.mods_dir
        pos = event.position().toPoint()
        mapped_pos = self.scroll_area.widget().mapFrom(self, pos)

        for cat_frame, _, content_frame, mod_info in self.category_refs:
            if cat_frame.geometry().contains(mapped_pos) or (
                    content_frame.isVisible() and content_frame.geometry().contains(mapped_pos)):
                target_dir = mod_info.path
                break

        self._process_zip_install(urls, target_dir)

    def _install_zip_via_dialog(self):
        if not self.current_version:
            return

        paths, _ = QtWidgets.QFileDialog.getOpenFileNames(
            self,
            "选择 Mod Zip文件",
            "",
            "Zip Files (*.zip)"
        )
        if paths:
            self._process_zip_install(paths, self.current_version.mods_dir)

    def _process_zip_install(self, zip_paths: List[str], target_dir: Path):
        self._start_loading("正在解压安装...")

        for zip_path in zip_paths:
            self._install_single_zip(Path(zip_path), target_dir)

        self.reload_mods()
        self._stop_loading()

    def _install_single_zip(self, zip_path: Path, target_dir: Path, force_replace: bool = False):
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            try:
                with zipfile.ZipFile(zip_path, 'r') as z:
                    z.extractall(temp_path)

                manifest_files = list(temp_path.rglob("manifest.json")) or list(
                    temp_path.rglob("manifest.json.disabled"))

                if not manifest_files:
                    dlg = QtWidgets.QMessageBox(self)
                    dlg.setWindowTitle("安装失败")
                    dlg.setText(f"{zip_path.name} 不是一个有效的模组。")
                    dlg.setInformativeText("未找到 manifest")
                    dlg.setIcon(QtWidgets.QMessageBox.Icon.Warning)
                    dlg.exec()
                    return

                for manifest_file in manifest_files:
                    mod_root = manifest_file.parent
                    if "__MACOSX" in str(mod_root):
                        continue

                    try:
                        data = json5.loads(manifest_file.read_text(encoding="utf-8-sig"))
                        unique_id = data.get("UniqueID", "")
                        mod_name = data.get("Name", mod_root.name)
                    except Exception:
                        continue

                    existing_mod = self._find_mod_by_id(unique_id)
                    final_dest = target_dir / mod_root.name

                    if existing_mod:
                        final_dest = existing_mod.path

                        if force_replace:
                            old_config = {}
                            old_config_path = final_dest / "config.json"
                            if old_config_path.exists():
                                try:
                                    old_config = json5.loads(old_config_path.read_text(encoding="utf-8-sig"))
                                except Exception:
                                    old_config = {}

                            shutil.rmtree(final_dest, ignore_errors=True)
                            shutil.copytree(mod_root, final_dest)

                            if old_config:
                                new_config_path = final_dest / "config.json"
                                if new_config_path.exists():
                                    try:
                                        new_config = json5.loads(new_config_path.read_text(encoding="utf-8-sig"))
                                        merged_config = deep_merge_dict(new_config, old_config)
                                        new_config_path.write_text(
                                            json.dumps(merged_config, ensure_ascii=False, indent=2),
                                            encoding="utf-8"
                                        )
                                    except Exception:
                                        new_config_path.write_text(
                                            json.dumps(old_config, ensure_ascii=False, indent=2),
                                            encoding="utf-8"
                                        )
                                else:
                                    new_config_path.write_text(
                                        json.dumps(old_config, ensure_ascii=False, indent=2),
                                        encoding="utf-8"
                                    )
                            continue

                        conflict = ConfigConflictDialog(mod_name, self)
                        conflict.exec()
                        choice = conflict.choice

                        if choice == "cancel":
                            continue

                        old_config = {}
                        old_config_path = final_dest / "config.json"
                        if old_config_path.exists():
                            try:
                                old_config = json5.loads(old_config_path.read_text(encoding="utf-8-sig"))
                            except Exception:
                                old_config = {}

                        shutil.rmtree(final_dest, ignore_errors=True)
                        shutil.copytree(mod_root, final_dest)

                        if choice == "merge":
                            new_config_path = final_dest / "config.json"
                            if new_config_path.exists():
                                try:
                                    new_config = json5.loads(new_config_path.read_text(encoding="utf-8-sig"))
                                    merged_config = deep_merge_dict(new_config, old_config)
                                    new_config_path.write_text(
                                        json.dumps(merged_config, ensure_ascii=False, indent=2),
                                        encoding="utf-8"
                                    )
                                except Exception:
                                    # 兜底：至少保留旧 config
                                    new_config_path.write_text(
                                        json.dumps(old_config, ensure_ascii=False, indent=2),
                                        encoding="utf-8"
                                    )
                            elif old_config:
                                new_config_path.write_text(
                                    json.dumps(old_config, ensure_ascii=False, indent=2),
                                    encoding="utf-8"
                                )
                    else:
                        if final_dest.exists():
                            shutil.rmtree(final_dest, ignore_errors=True)
                        shutil.copytree(mod_root, final_dest)

            except Exception as e:
                dlg = QtWidgets.QMessageBox(self)
                dlg.setWindowTitle("错误")
                dlg.setText(f"安装 {zip_path.name} 时出错")
                dlg.setInformativeText(str(e))
                dlg.setIcon(QtWidgets.QMessageBox.Icon.Critical)
                dlg.exec()

    def _find_mod_by_id(self, unique_id: str) -> Optional[ModInfo]:
        def search(mods):
            for m in mods:
                if m.is_category:
                    res = search(m.children)
                    if res: return res
                elif m.unique_id == unique_id:
                    return m
            return None

        return search(self.all_mods)

    def _toggle_fold_all(self):
        self._all_expanded = not self._all_expanded
        self.btn_toggle_fold.setText("↕ 全部折叠" if self._all_expanded else "↕ 全部展开")
        for cat_frame, _, content_frame, _ in self.category_refs:
            content_frame.setVisible(self._all_expanded)
            cat_label = cat_frame.findChild(QtWidgets.QLabel)
            if cat_label:
                text = cat_label.text()
                new_text = text.replace("▶", "▼") if self._all_expanded else text.replace("▼", "▶")
                cat_label.setText(new_text)

    def _animate_update_btn(self):
        self._spinner_idx = (self._spinner_idx + 1) % len(self._spinner_frames)
        self.btn_check_update.setText(f"{self._spinner_frames[self._spinner_idx]} 检查中...")

    def _check_mod_updates(self):
        if self._update_thread and self._update_thread.isRunning(): return
        self.btn_check_update.setEnabled(False)
        self._update_timer.start(100)

        flat_mods = []

        def flatten(mods):
            for m in mods:
                if m.is_category:
                    flatten(m.children)
                else:
                    flat_mods.append(m)

        flatten(self.all_mods)

        self._update_thread = UpdateCheckThread(flat_mods, nexus_api_key=self.nexus_api_key)
        self._update_thread.update_found.connect(self._on_update_found)
        self._update_thread.finished_check.connect(self._on_update_finished)
        self._update_thread.start()

    def _on_update_found(self, unique_id: str, new_version: str):
        for w in self.mod_widgets:
            if w.mod.unique_id == unique_id:
                w.ver_lbl.setText(f"v{w.mod.version} -> {new_version}")
                w.ver_lbl.setStyleSheet(
                    "color: white; font-size: 11px; background: #10B981; padding: 2px 6px; border-radius: 4px; font-weight: bold;")

    def _on_update_finished(self, success: bool):
        self._update_timer.stop()
        self.btn_check_update.setEnabled(True)
        if success:
            self.btn_check_update.setText("✅ 检查完成")
            self.btn_check_update.setStyleSheet(
                "QPushButton { background: #D1FAE5; border: 1px solid #10B981; color: #065F46; border-radius: 6px; padding: 0 12px; font-size: 13px; font-weight: bold; }")
        else:
            self.btn_check_update.setText("❌ 网络超时")
            self.btn_check_update.setStyleSheet(
                "QPushButton { background: #FEE2E2; border: 1px solid #EF4444; color: #991B1B; border-radius: 6px; padding: 0 12px; font-size: 13px; font-weight: bold; }")

        QtCore.QTimer.singleShot(8000, self._reset_update_btn)

    def _reset_update_btn(self):
        self.btn_check_update.setText("🔄 检查更新")
        self.btn_check_update.setStyleSheet(
            "QPushButton { background: #ffffff; border: 1px solid #d1d5db; border-radius: 6px; padding: 0 12px; font-size: 13px; color: #374151; } QPushButton:hover { background: #f3f4f6; }")

    def _nexus_headers(self) -> dict:
        headers = {
            "User-Agent": "StardewLauncher/1.0",
            "Accept": "application/json",
        }
        if self.nexus_api_key:
            headers["apikey"] = self.nexus_api_key
        return headers

    def _extract_numeric_id(self, nexus_id: str) -> Optional[int]:
        if not nexus_id:
            return None
        m = re.search(r'(\d+)', str(nexus_id))
        if not m:
            return None
        try:
            return int(m.group(1))
        except Exception:
            return None

    def _fetch_nexus_game_id(self) -> Optional[int]:
        if hasattr(self, "_cached_nexus_game_id"):
            return self._cached_nexus_game_id

        payload = {
            "query": "query game($domainName: String) { game(domainName: $domainName) { id } }",
            "variables": {"domainName": "stardewvalley"},
        }

        try:
            resp = requests.post(
                "https://api.nexusmods.com/v2/graphql",
                json=payload,
                headers=self._nexus_headers(),
                timeout=15,
            )
            resp.raise_for_status()
            data = resp.json()
            game = (data.get("data") or {}).get("game") or {}
            game_id = game.get("id")
            self._cached_nexus_game_id = int(game_id)
        except Exception as e:
            logger.debug("Failed to fetch Nexus game id: %s", e)
            self._cached_nexus_game_id = None

        return self._cached_nexus_game_id

    def _fetch_latest_nexus_file_info(self, mod_id: int, local_version: str) -> Optional[dict]:
        game_id = self._fetch_nexus_game_id()
        if not game_id:
            return None

        payload = {
            "query": (
                "query modFiles($modId: ID!, $gameId: ID!) { "
                "modFiles(modId: $modId, gameId: $gameId) { "
                "category primary uri version name date fileId } }"
            ),
            "variables": {"modId": mod_id, "gameId": game_id},
        }

        try:
            resp = requests.post(
                "https://api.nexusmods.com/v2/graphql",
                json=payload,
                headers=self._nexus_headers(),
                timeout=20,
            )
            resp.raise_for_status()
            data = resp.json()
            files = ((data.get("data") or {}).get("modFiles") or [])
        except Exception as e:
            logger.debug("Failed to fetch Nexus mod files for %s: %s", mod_id, e)
            return None

        if not files:
            return None

        def norm(v) -> str:
            return str(v or "").strip()

        def score(file_obj: dict) -> tuple:
            category = norm(file_obj.get("category")).upper()
            primary = 1 if str(file_obj.get("primary", "")).lower() in {"1", "true", "yes"} else 0
            try:
                date = int(file_obj.get("date") or 0)
            except Exception:
                date = 0
            try:
                version_newer = 1 if norm(file_obj.get("version")) and is_newer_version(local_version, norm(
                    file_obj.get("version"))) else 0
            except Exception:
                version_newer = 0
            return (version_newer, 1 if category in {"MAIN", "UPDATE"} else 0, primary, date)

        candidates = [f for f in files if norm(f.get("uri"))]
        if not candidates:
            return None

        candidates.sort(key=score, reverse=True)
        return candidates[0]

    def _get_nexus_download_url(self, mod_id: int, file_id: int) -> Optional[str]:
        url = f"https://api.nexusmods.com/v1/games/stardewvalley/mods/{mod_id}/files/{file_id}/download_link.json"

        try:
            resp = requests.get(
                url,
                headers=self._nexus_headers(),
                timeout=20
            )
            resp.raise_for_status()
            data = resp.json()

            if isinstance(data, list) and data:
                return data[0].get("URI")

        except Exception as e:
            logger.exception("Failed to get download link: %s", e)

        return None

    def _download_nexus_zip(self, url: str, label: str = "") -> Optional[Path]:
        url = (url or "").strip()

        if not url:
            logger.error("Nexus download url is empty: %s", label or "<unknown>")
            return None

        parsed = urlparse(url)
        if parsed.scheme not in {"http", "https"}:
            logger.error("Nexus returned non-absolute download url for %s: %r", label or "<unknown>", url)
            return None

        tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".zip")
        tmp_path = Path(tmp.name)
        tmp.close()

        try:
            with requests.get(
                    url,
                    headers=self._nexus_headers(),
                    timeout=120,
                    stream=True,
                    allow_redirects=True,
            ) as resp:
                resp.raise_for_status()
                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=1024 * 256):
                        if chunk:
                            f.write(chunk)
            return tmp_path
        except Exception as e:
            logger.exception("Failed to download Nexus zip %s: %s", label or url, e)
            try:
                if tmp_path.exists():
                    tmp_path.unlink()
            except Exception:
                pass
            return None

    def _update_selected_mods(self):
        if not self.current_version:
            QtWidgets.QMessageBox.information(self, "未选择版本", "请先选择一个可安装 Mod 的版本。")
            return

        selected_mods = [m for m in self.selected_mods if not m.is_category]
        if not selected_mods:
            QtWidgets.QMessageBox.information(self, "未选择模组", "请先在列表中选中一个或多个 Mod。")
            return

        if self._mod_update_thread and self._mod_update_thread.isRunning():
            QtWidgets.QMessageBox.information(self, "正在更新", "模组正在更新中，请稍候。")
            return

        self._start_loading("正在后台更新选中的 Mod...")
        self.btn_mass_update.setText("⏳ 更新中...")
        self.btn_mass_update.setEnabled(False)

        self._mod_update_thread = ModUpdateThread(selected_mods, nexus_api_key=self.nexus_api_key, parent=self)
        self._mod_update_result = (0, 0, 0, "")
        self._mod_update_thread.progress.connect(self._on_mod_update_progress)
        self._mod_update_thread.finished_update.connect(self._on_mod_update_finished)
        self._mod_update_thread.finished.connect(self._on_mod_update_thread_done)
        self._mod_update_thread.start()

    def _on_mod_update_progress(self, text: str):
        if hasattr(self, "_loading_label") and self._loading_label:
            self._loading_label.setText(text)

    def _on_mod_update_finished(self, updated: int, skipped: int, failed: int, info: str = ""):
        self._mod_update_result = (updated, skipped, failed, info)

    def _on_mod_update_thread_done(self):
        updated, skipped, failed, info = getattr(self, "_mod_update_result", (0, 0, 0, ""))
        self._mod_update_thread = None
        self._mod_update_result = (0, 0, 0, "")
        self._stop_loading()
        self.btn_mass_update.setText("更新")
        self.reload_mods()
        QtWidgets.QMessageBox.information(
            self,
            "更新完成",
            f"已更新 {updated} 个 Mod，跳过 {skipped} 个，失败 {failed} 个\n{info}",
        )

    def _build_tree(self, mods: List[ModInfo], parent_layout: QtWidgets.QVBoxLayout, indent_level: int = 0) -> List[
        ModItemWidget]:
        created = []
        for mod in mods:
            if mod.is_category:
                cat_frame = QtWidgets.QFrame()
                cat_frame.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)
                cat_layout = QtWidgets.QVBoxLayout(cat_frame)
                cat_layout.setContentsMargins(indent_level * 16, 8, 0, 8)

                cat_label = ClickableLabel(f"▼ 📂 {mod.name}")
                cat_label.setFixedHeight(40)
                cat_label.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
                cat_label.setStyleSheet("""
                    QLabel { font-weight: bold; color: #4B5563; font-size: 14px; background-color: rgba(240, 255, 255, 0.9); border-radius: 6px; padding: 4px 8px; }
                    QLabel:hover { background-color: rgba(220, 245, 245, 0.9); }
                """)
                cat_layout.addWidget(cat_label)

                content_frame = QtWidgets.QFrame()
                content_frame.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding,
                                            QtWidgets.QSizePolicy.Policy.Maximum)
                content_frame.setStyleSheet("border-left: 2px solid rgba(0,0,0,0.08); margin-left: 8px;")
                content_layout = QtWidgets.QVBoxLayout(content_frame)

                content_layout.setContentsMargins(0, 0, 0, 0)
                content_layout.setSpacing(6)

                children_widgets = self._build_tree(mod.children, content_layout, 0)

                cat_layout.addWidget(content_frame)
                parent_layout.addWidget(cat_frame)

                # 折叠功能
                def toggle_folder(cf=content_frame, lbl=cat_label, text=mod.name):
                    visible = not cf.isVisible()
                    cf.setVisible(visible)
                    lbl.setText(f"▼ 📂 {text}" if visible else f"▶ 📂 {text}")

                cat_label.clicked.connect(toggle_folder)

                self.category_refs.append((cat_frame, children_widgets, content_frame, mod))
                created.extend(children_widgets)
            else:
                widget = ModItemWidget(mod)
                widget.selection_changed.connect(self._on_mod_toggled)
                widget.open_folder.connect(self._open_mod_folder)
                widget.open_web.connect(self._open_mod_web)
                widget.show_details.connect(self._show_mod_details)
                widget.open_settings.connect(self._show_mod_settings)
                self.mod_widgets.append(widget)
                created.append(widget)

                if indent_level > 0:
                    container = QtWidgets.QWidget()
                    l = QtWidgets.QVBoxLayout(container)
                    l.setContentsMargins(indent_level * 16, 0, 0, 0)
                    l.setSpacing(0)
                    l.addWidget(widget)
                    parent_layout.addWidget(container)
                    widget._container = container
                else:
                    parent_layout.addWidget(widget)
                    widget._container = widget
        return created

    def _start_loading(self, text: str = "正在加载 Mod，请稍候..."):
        self.btn_open_mods.setEnabled(False)
        self.btn_download.setEnabled(False)
        self.btn_select_all.setEnabled(False)
        self.btn_refresh_mod.setEnabled(False)
        self.btn_check_update.setEnabled(False)
        self.btn_mass_update.setEnabled(False)

        if not hasattr(self, "_loading_overlay") or self._loading_overlay is None:
            self._loading_overlay = QtWidgets.QFrame(self.scroll_area.viewport())
            self._loading_overlay.setStyleSheet("""
                QFrame {
                    background: rgba(255, 255, 255, 0.25);
                    border: 1px solid rgba(0,0,0,0.06);
                    border-radius: 16px;
                }
                QLabel {
                    color: #374151;
                    font-size: 13px;
                    font-weight: 700;
                }
            """)
            overlay_layout = QtWidgets.QVBoxLayout(self._loading_overlay)
            overlay_layout.setContentsMargins(18, 18, 18, 18)
            overlay_layout.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)

            self._loading_label = QtWidgets.QLabel(text)
            self._loading_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
            self._loading_label.setStyleSheet("""
                QLabel {
                    background-color: rgba(200, 255, 255, 150);
                    border-radius: 10px;                       /* 圆角 */
                    color: #333333;                            /* 深灰文字，避免纯黑过硬 */
                    font-size: 14px;                           /* 字体大小 */
                    padding: 8px 12px;                         /* 内边距 */
                }
            """)
            overlay_layout.addWidget(self._loading_label)

        self._loading_label.setText(text)
        self._loading_overlay.setGeometry(self.scroll_area.viewport().rect())
        self._loading_overlay.raise_()
        self._loading_overlay.show()
        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.CursorShape.WaitCursor)

    def _stop_loading(self):
        self.btn_open_mods.setEnabled(True)
        self.btn_download.setEnabled(True)
        self.btn_select_all.setEnabled(True)
        self.btn_refresh_mod.setEnabled(True)
        self.btn_check_update.setEnabled(True)
        self.btn_mass_update.setEnabled(True)

        if hasattr(self, "_loading_overlay") and self._loading_overlay:
            self._loading_overlay.hide()

        QtWidgets.QApplication.restoreOverrideCursor()

    def resizeEvent(self, event: QtGui.QResizeEvent):
        super().resizeEvent(event)
        w = min(500, self.width() - 40)
        x = (self.width() - w) // 2
        y = self.height() - self.bottom_bar.height() - 20
        self.bottom_bar.setGeometry(x, y, w, self.bottom_bar.height())

    def load_version(self, version: GameVersion, global_notes: Dict[str, str]):
        self.current_version = version
        self.global_notes = global_notes
        self.title_label.setText(f"Mod 管理: {version.name}")
        self.reload_mods()

    def reload_mods(self):
        if not self.current_version: return
        self._start_loading()
        self._clear_list()
        self.selected_mods.clear()
        self._update_bottom_bar()

        mods_dir = self.current_version.mods_dir
        if not mods_dir.exists(): mods_dir.mkdir(parents=True, exist_ok=True)
        self.all_mods = parse_mod_directory(mods_dir, self.global_notes)
        self._build_tree(self.all_mods, self.list_layout)
        self._update_tabs_count()
        self._apply_filters()
        self._stop_loading()

    def _clear_list(self):
        self.mod_widgets.clear()
        self.category_refs.clear()
        layout = self.list_layout
        while layout.count():
            item = layout.takeAt(0)
            if item is None: break
            w = item.widget()
            if w:
                w.setParent(None)
                w.deleteLater()

    # ---------- Update Checks ----------
    # def _check_updates(self):
    #     self.btn_check_update.setText("⏳ 正在检查...")
    #     self.btn_check_update.setEnabled(False)
    #     self.btn_check_update.setStyleSheet(
    #         "background: #FEF3C7; color: #D97706; border: 1px solid #FCD34D; border-radius: 6px; padding: 0 12px; font-size: 13px;")
    #
    #     flat_mods = []
    #
    #     def gather(ml):
    #         for m in ml:
    #             if m.is_category:
    #                 gather(m.children)
    #             else:
    #                 flat_mods.append(m)
    #
    #     gather(self.all_mods)
    #
    #     self.update_thread = UpdateCheckThread(flat_mods)
    #     self.update_thread.finished_check.connect(self._on_update_check_finished)
    #     self.update_thread.start()
    #
    # def _on_update_check_finished(self, updates: dict, success: bool):
    #     if success:
    #         self.btn_check_update.setText("✅ 检查完成")
    #         self.btn_check_update.setStyleSheet(
    #             "background: #D1FAE5; color: #059669; border: 1px solid #A7F3D0; border-radius: 6px; padding: 0 12px; font-size: 13px;")
    #         for widget in self.mod_widgets:
    #             if widget.mod.unique_id in updates:
    #                 widget.mod.has_update = True
    #                 widget.mod.new_version = updates[widget.mod.unique_id]
    #                 widget._update_style()
    #     else:
    #         self.btn_check_update.setText("❌ 网络超时")
    #         self.btn_check_update.setStyleSheet(
    #             "background: #FEE2E2; color: #DC2626; border: 1px solid #FECACA; border-radius: 6px; padding: 0 12px; font-size: 13px;")
    #
    #     self.btn_check_update.setEnabled(True)
    #     QtCore.QTimer.singleShot(3000, self._reset_check_btn)

    # def _reset_check_btn(self):
    #     self.btn_check_update.setText("🔄 检查更新")
    #     self.btn_check_update.setStyleSheet(
    #         "QPushButton { background: #ffffff; border: 1px solid #d1d5db; border-radius: 6px; padding: 0 12px; font-size: 13px; color: #374151; } QPushButton:hover { background: #f3f4f6; }")

    # ---------- Rest of ModManager ----------
    def _show_mod_settings(self, mod: ModInfo):
        config_path = mod.path / "config.json"
        if not config_path.exists():
            QtWidgets.QMessageBox.information(self, "未找到配置",
                                              f"该模组 ({mod.name}) 没有找到可用的 config.json 配置文件。")
            return
        # 假设 ModConfigDialog 在上下文中可用
        dlg = ModConfigDialog(config_path, mod.name, self)
        dlg.exec()

    def _show_mod_details(self, mod: ModInfo):
        dlg = ModDetailDialog(mod, self)
        dlg.note_saved.connect(lambda note: self._on_mod_note_saved(mod, note))
        dlg.exec()

    def _on_mod_note_saved(self, mod: ModInfo, new_note: str):
        mod.note = new_note
        mod._search_blob = None
        note_key = mod.unique_id if mod.unique_id else str(mod.path)
        self.mod_note_changed.emit(note_key, new_note)
        for w in self.mod_widgets:
            if w.mod == mod:
                w._update_style()
                break

    def _update_tabs_count(self):
        total = len(self.mod_widgets)
        enabled = sum(1 for w in self.mod_widgets if w.mod.is_enabled)
        disabled = total - enabled
        self.btn_tab_all.setText(f"全部 ({total})")
        self.btn_tab_enabled.setText(f"已启用 ({enabled})")
        self.btn_tab_disabled.setText(f"已禁用 ({disabled})")

    def _on_tab_toggled(self, id: int, checked: bool):
        if not checked: return
        self.current_filter = ["all", "enabled", "disabled"][id]
        self._apply_filters()

    def _apply_filters(self):
        search_text = self.search_input.text().strip()
        for w in self.mod_widgets:
            mod: ModInfo = w.mod
            m_filter = True
            if self.current_filter == "enabled" and not mod.is_enabled: m_filter = False
            if self.current_filter == "disabled" and mod.is_enabled: m_filter = False
            m_search = mod.matches_search(search_text)

            should_show = m_filter and m_search
            w._should_show = should_show
            w._container.setVisible(should_show)

        for cat_frame, children, content_frame, _ in reversed(self.category_refs):
            cat_should_show = any(getattr(cw, "_should_show", True) for cw in children)
            cat_frame.setVisible(cat_should_show)

    def _on_mod_toggled(self, checked: bool, mod: ModInfo):
        if checked:
            self.selected_mods.add(mod)
        else:
            self.selected_mods.discard(mod)
        self._update_bottom_bar()

    def _update_bottom_bar(self):
        count = len(self.selected_mods)
        if count > 0:
            self.lbl_selected_count.setText(f"已选择 {count} 个")
            self.bottom_bar.show()
            self.bottom_bar.raise_()
        else:
            self.bottom_bar.hide()

    def _select_all_visible(self):
        visible_widgets = [w for w in self.mod_widgets if w._container.isVisible()]
        if not visible_widgets: return
        all_selected = all(w.selected for w in visible_widgets)
        for w in visible_widgets:
            w.toggle_selection(not all_selected)

    def _clear_selection(self):
        for w in self.mod_widgets:
            if w.selected: w.toggle_selection(False)
        self.selected_mods.clear()
        self._update_bottom_bar()

    def _mass_action(self, action: str):
        if not self.selected_mods:
            return

        if action == "delete":
            selected_mods = [m for m in self.selected_mods if not m.is_category]
            if not selected_mods:
                QtWidgets.QMessageBox.information(self, "未选择模组", "请先在列表中选中一个或多个 Mod。")
                return

            dlg = DeleteConfirmDialog(
                "删除 Mod",
                f"确定要删除选中的 {len(selected_mods)} 个 Mod 吗？",
                self
            )
            # dlg = DeleteConfirmDialog(
            #     "删除 Mod",
            #     f"确定要删除选中的 {len(selected_mods)} 个 Mod 吗？<br>"
            #     "系统会先将每个模组压缩到其自身目录下的 <b>.backup</b> 文件夹，再执行删除。<br>"
            #     "该操作不可逆！",
            #     self
            # )
            if dlg.exec() != QtWidgets.QDialog.DialogCode.Accepted:
                return

            deleted_count = 0
            failed_items: list[str] = []

            for mod in selected_mods:
                try:
                    if not mod.path.exists():
                        failed_items.append(f"{mod.name}：目录不存在")
                        continue

                    backup_path = backup_mod_folder(mod.path, self.current_version.mods_dir)
                    if not backup_path or not backup_path.exists():
                        failed_items.append(f"{mod.name}：备份失败")
                        continue

                    self._remove_mod_contents_preserving_backup(mod.path, mod.name)
                    deleted_count += 1

                except Exception as e:
                    logger.exception("Failed to backup/delete mod %s: %s", mod.name, e)
                    failed_items.append(f"{mod.name}：{e}")

            self.reload_mods()

            if failed_items:
                QtWidgets.QMessageBox.warning(
                    self,
                    "部分操作失败",
                    f"已删除 {deleted_count} 个 Mod。<br><br>以下项目失败：<br>"
                    + "<br>".join(failed_items)
                )
            else:
                pass
                # QtWidgets.QMessageBox.information(
                #     self,
                #     "操作完成",
                #     f"已成功备份并删除 {deleted_count} 个 Mod。"
                # )
            return

        for mod in self.selected_mods:
            try:
                manifest_en = mod.path / "manifest.json"
                manifest_dis = mod.path / "manifest.json.disabled"
                changed = False
                if action == "enable" and not mod.is_enabled:
                    if manifest_dis.exists(): manifest_dis.rename(manifest_en)
                    mod.is_enabled = True
                    changed = True
                elif action == "disable" and mod.is_enabled:
                    if manifest_en.exists(): manifest_en.rename(manifest_dis)
                    mod.is_enabled = False
                    changed = True
                if changed:
                    for w in self.mod_widgets:
                        if w.mod == mod: w._update_style()
            except Exception as e:
                logger.error(f"Error acting on {mod.name}: {e}")

        self._update_tabs_count()
        self._apply_filters()
        self._clear_selection()

    def _remove_mod_contents_preserving_backup(self, mod_path: Path, mod_name: str) -> None:
        """
        删除模组内容，但保留 .backup 目录及其中的备份文件。
        这样可满足“先备份，再删除模组内容”的需求，同时不丢失备份包。
        """
        # mods_dir = self.current_version.mods_dir
        # backup_dir = mods_dir / ".backup"

        if not mod_path.exists() or not mod_path.is_dir():
            return

        manifest = mod_path / "manifest.json"
        manifest_disabled = mod_path / "manifest.json.disabled"
        if not (manifest.exists() or manifest_disabled.exists()):
            return

        try:
            shutil.rmtree(mod_path)
        except Exception as e:
            logger.exception("Failed to remove mod %s: %s", mod_path, e)

        # for child in list(mod_path.iterdir()):
        #     print(child.name)
        #     if child == backup_dir or backup_dir in child.parents:
        #         continue
        #     try:
        #         # if child.is_dir():
        #         #     shutil.rmtree(child)
        #         # else:
        #         #     child.unlink()
        #     except Exception as e:
        #         logger.exception("Failed to remove mod item %s: %s", child, e)

    def _open_mods_folder(self):
        self.btn_open_mods.setEnabled(False)

        if self.current_version: open_in_file_explorer(self.current_version.mods_dir)

        QtCore.QTimer.singleShot(2000, lambda: self.btn_open_mods.setEnabled(True))

    def _open_mod_folder(self, mod_item: ModItemWidget):
        mod_item.btn_folder.setEnabled(False)

        open_in_file_explorer(mod_item.mod.path)

        QtCore.QTimer.singleShot(2000, lambda: mod_item.btn_folder.setEnabled(True))

    def _download_mods(self):
        webbrowser.open("https://www.nexusmods.com/stardewvalley")

    def _open_mod_web(self, mod: ModInfo):
        if mod.nexus_id:
            webbrowser.open(f"https://www.nexusmods.com/stardewvalley/mods/{mod.nexus_id}")
        else:
            webbrowser.open(f"https://www.nexusmods.com/stardewvalley/search/?gsearch={mod.name.replace(' ', '+')}")


# ===== A3 / 定位：替换 class SaveRow 的定义头部与 __init__ =====
class SaveRow(QtWidgets.QWidget):
    meta_changed = QtCore.Signal(str, str, str, str, str, str)
    # name, version_id, note, icon_path, icon_source, icon_version_id
    clicked = QtCore.Signal(str)

    def __init__(
            self,
            save_name: str,
            available_versions: List[GameVersion],
            current_version_id: str,
            current_note: str,
            current_icon: str,
            icon_source: str = ICON_SOURCE_NONE,
            icon_version_id: str = "",
            parent=None
    ):
        super().__init__(parent)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setObjectName("saveRow")
        self.save_name = save_name
        self.available_versions = available_versions
        self.current_icon = current_icon or ""
        self.icon_source = icon_source or ICON_SOURCE_NONE
        self.icon_version_id = icon_version_id or ""
        self.current_version_id = current_version_id
        self.current_note = current_note
        self.setMinimumHeight(90)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self._init_ui(current_version_id, current_note)

    def _init_ui(self, current_version_id: str, current_note: str):
        layout = QtWidgets.QHBoxLayout(self)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(16)

        self.icon_label = QtWidgets.QLabel()
        self.icon_label.setFixedSize(64, 64)
        apply_icon_to_label(self.icon_label, self.current_icon, 64)
        if not self.current_icon:
            self._set_default_icon()
        layout.addWidget(self.icon_label)

        text_box = QtWidgets.QVBoxLayout()
        text_box.setSpacing(4)

        self.name_label = QtWidgets.QLabel(self.save_name)
        self.name_label.setStyleSheet("font-weight: 800; font-size: 15px; color: #111827;")
        text_box.addWidget(self.name_label)

        self.name_scroll = QtWidgets.QWidget()
        self.name_scroll.setLayout(text_box)
        self.name_scroll.setFixedWidth(190)  # 让右侧输入框起始位置稳定
        layout.addWidget(self.name_scroll)

        right_layout = QtWidgets.QVBoxLayout()
        right_layout.setSpacing(8)
        right_layout.setAlignment(QtCore.Qt.AlignmentFlag.AlignVCenter)

        self.combo_version = NoWheelComboBox()
        self.combo_version.setCursor(QtCore.Qt.CursorShape.ArrowCursor)
        self.combo_version.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
        self.combo_version.setMinimumWidth(250)
        self.combo_version.addItem("未绑定版本", userData="")

        for v in self.available_versions:
            self.combo_version.addItem(v.name, userData=v.id)
            if v.id == current_version_id:
                self.combo_version.setCurrentIndex(self.combo_version.count() - 1)

        self.input_note = QtWidgets.QLineEdit()
        self.input_note.setCursor(QtCore.Qt.CursorShape.IBeamCursor)
        self.input_note.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)
        self.input_note.setMinimumWidth(250)
        self.input_note.setPlaceholderText("在此处添加存档备注...")
        self.input_note.setText(current_note)

        right_layout.addWidget(self.combo_version)
        right_layout.addWidget(self.input_note)
        layout.addLayout(right_layout, stretch=1)

        self.setStyleSheet("""
            QWidget#saveRow { background-color: rgba(255, 255, 255, 0.6); border: 1px solid rgba(125, 255, 255, 0.35); border-radius: 12px; }
            QWidget#saveRow:hover { background-color: rgba(255, 255, 255, 0.82); border: 1px solid rgba(43,123,228,0.35); }
            QComboBox, QLineEdit { border: 1px solid #D1D5DB; border-radius: 8px; padding: 6px 12px; background-color: rgba(255, 255, 255, 0.82); color: #333; font-size: 13px; }
            QComboBox:hover, QLineEdit:hover, QComboBox:focus, QLineEdit:focus { border-color: #2B7BE4; background-color: rgba(255, 255, 255, 0.95); }
            QComboBox::drop-down { border: none; width: 28px; }
        """)
        self.combo_version.currentIndexChanged.connect(self._on_version_changed)
        self.input_note.editingFinished.connect(self._on_changed)

    # def _set_default_icon(self):
    #     pix = QtGui.QPixmap(48, 48)
    #     pix.fill(QtCore.Qt.GlobalColor.transparent)
    #     painter = QtGui.QPainter(pix)
    #     painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
    #     painter.setBrush(QtGui.QColor(200, 200, 200))
    #     painter.setPen(QtCore.Qt.PenStyle.NoPen)
    #     painter.drawRoundedRect(pix.rect(), 8, 8)
    #     painter.end()
    #     self.icon_label.setPixmap(pix)

    def _set_default_icon(self):
        self.icon_label.clear()
        self.icon_label.setPixmap(QtGui.QPixmap())

    def mouseReleaseEvent(self, event):
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            child = self.childAt(event.position().toPoint())
            if not isinstance(child, (QtWidgets.QLineEdit, QtWidgets.QComboBox)):
                self.clicked.emit(self.save_name)
        super().mouseReleaseEvent(event)

    def _on_version_changed(self):
        v_id = self.combo_version.currentData() or ""
        # 兼容旧数据：把“预设: 无”视为真正的“未设置图标”
        icon_is_effectively_none = (
                not self.current_icon
                or (is_preset(self.current_icon) and self.current_icon[len(PRESET_STR):] == "无")
        )

        # 仅当当前图标是“无”或来自版本绑定时，才自动切换为当前版本图标
        if self.icon_source != ICON_SOURCE_CUSTOM or icon_is_effectively_none:
            bound_icon = resolve_version_icon_path(v_id, self.available_versions)
            if bound_icon:
                self.current_icon = bound_icon
                self.icon_source = ICON_SOURCE_VERSION
                self.icon_version_id = v_id
                apply_icon_to_label(self.icon_label, self.current_icon, 64)
            else:
                self.current_icon = ""
                self.icon_source = ICON_SOURCE_NONE
                self.icon_version_id = ""
                self._set_default_icon()

        self._on_changed()

    def _on_changed(self):
        v_id = self.combo_version.currentData() or ""
        self.meta_changed.emit(
            self.save_name,
            v_id,
            self.input_note.text(),
            self.current_icon,
            self.icon_source,
            self.icon_version_id,
        )


class SaveDetailPage(QtWidgets.QWidget):
    back_requested = QtCore.Signal()
    backup_requested = QtCore.Signal(str)
    delete_requested = QtCore.Signal(str)
    icon_changed = QtCore.Signal(str, str)
    icon_history_removed = QtCore.Signal(str)
    open_folder_requested = QtCore.Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.save_name = ""
        self._init_ui()

    def _init_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(16)

        top_nav = QtWidgets.QHBoxLayout()
        self.btn_back = QtWidgets.QPushButton("← 返回")
        self.btn_back.setFixedSize(85, 32)
        self.btn_back.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_back.setStyleSheet("""
            QPushButton {
                background-color: rgba(255, 255, 255, 0.7);
                border: 1px solid rgba(255, 255, 255, 0.6);
                border-radius: 12px;
                padding: 6px 8px;
                color: #222;
                font-weight: 500;
            }

            QPushButton:hover {
                background-color: rgba(255, 255, 255, 0.8);
            }

            QPushButton:pressed {
                background-color: rgba(255, 255, 255, 0.5);
            }
        """)
        self.btn_back.clicked.connect(self.back_requested.emit)

        top_nav.addWidget(self.btn_back)
        top_nav.addSpacing(0)
        self.title_label = QtWidgets.QLabel("💾 存档详情")
        self.title_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.title_label.setFixedHeight(36)
        self.title_label.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Maximum,
            QtWidgets.QSizePolicy.Policy.Fixed
        )
        self.title_label.setStyleSheet("""
            QLabel {
                background: rgba(255, 255, 255, 0.8);
                border-radius: 12px;
                padding: 6px 16px;
                font-size: 15px;
                font-weight: 600;
                color: #374151;
                border: 1px solid rgba(0, 0, 0, 0.06);
            }
        """)

        top_nav.addWidget(self.title_label)
        top_nav.addStretch()
        layout.addLayout(top_nav)

        # ================= 头部卡片 =================
        header_card = QtWidgets.QFrame()
        header_card.setObjectName("headerCard")
        header_card.setStyleSheet("""
            QFrame#headerCard {
                background: rgba(255, 255, 255, 0.65);
                border-radius: 16px;
                border: 1px solid rgba(0, 0, 0, 0.06);
            }
        """)

        header_layout = QtWidgets.QHBoxLayout(header_card)
        header_layout.setContentsMargins(16, 16, 16, 16)
        header_layout.setSpacing(14)

        self.icon_label = QtWidgets.QLabel()
        self.icon_label.setFixedSize(64, 64)
        self.icon_label.setStyleSheet("""
            QLabel {
                background: rgba(255,255,255,0.9);
                border-radius: 12px;
                border: 1px solid rgba(0,0,0,0.08);
            }
        """)
        header_layout.addWidget(self.icon_label)

        title_wrap = QtWidgets.QVBoxLayout()
        title_wrap.setSpacing(4)

        self.name_label = QtWidgets.QLabel()
        self.name_label.setWordWrap(True)
        self.name_label.setStyleSheet("""
            font-size: 18px;
            font-weight: 700;
            color: #111827;
        """)

        self.meta_label = QtWidgets.QLabel()
        self.meta_label.setWordWrap(True)
        self.meta_label.setStyleSheet("""
            font-size: 12px;
            color: #6B7280;
        """)

        title_wrap.addWidget(self.name_label)
        title_wrap.addWidget(self.meta_label)

        header_layout.addLayout(title_wrap, 1)
        layout.addWidget(header_card)

        # ================= 表单卡片 =================
        form_card = QtWidgets.QFrame()
        form_card.setObjectName("formCard")
        form_card.setStyleSheet("""
            QFrame#formCard {
                background: rgba(255, 255, 255, 0.6);
                border-radius: 16px;
                border: 1px solid rgba(0, 0, 0, 0.06);
            }
        """)

        form_wrap = QtWidgets.QVBoxLayout(form_card)
        form_wrap.setContentsMargins(16, 16, 16, 16)

        form = QtWidgets.QFormLayout()
        form.setVerticalSpacing(12)
        form.setLabelAlignment(QtCore.Qt.AlignmentFlag.AlignLeft)

        self.combo_icon = HistoryComboBox()
        self.combo_icon.setFixedHeight(34)
        self.combo_icon.add_fixed_items(["📁 自定义图片...", "🎨 打开预设图库..."])
        self.combo_icon.activated.connect(self._on_icon_combo_activated)
        label_style = """
             QLabel {
                 color: #272320;
                 font-size: 13px;
                 font-weight: 550;
             }
         """
        self.setStyleSheet(self.styleSheet() + label_style)
        form.addRow("图标", self.combo_icon)

        form_wrap.addLayout(form)

        layout.addWidget(form_card)

        # ================= 操作按钮 =================
        action_row = QtWidgets.QHBoxLayout()
        action_row.setSpacing(10)

        common_btn = """
            QPushButton {
                border-radius: 12px;
                font-size: 14px;
                font-weight: 600;
                padding: 6px;
            }
        """

        self.btn_open_folder = QtWidgets.QPushButton("📁 打开文件夹")
        self.btn_open_folder.setStyleSheet(common_btn + """
            QPushButton {
                background: #2B7BE4;
                color: white;
            }
            QPushButton:hover {
                background: #1D4ED8;
            }
        """)

        self.btn_backup = QtWidgets.QPushButton("备份")
        self.btn_backup.setStyleSheet(common_btn + """
            QPushButton {
                background: #10B981;
                color: white;
            }
            QPushButton:hover {
                background: #059669;
            }
        """)

        self.btn_delete = QtWidgets.QPushButton("删除")
        self.btn_delete.setStyleSheet(common_btn + """
            QPushButton {
                background: rgba(255,255,255,0.9);
                color: #ef4444;
                border: 1px solid #ef4444;
            }
            QPushButton:hover {
                background: #fef2f2;
            }
        """)

        for btn in (self.btn_open_folder, self.btn_backup, self.btn_delete):
            btn.setFixedHeight(42)
            btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            btn.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Fixed)

        self.btn_open_folder.clicked.connect(self._open_save_folder)
        self.btn_backup.clicked.connect(lambda: self.backup_requested.emit(self.save_name))
        self.btn_delete.clicked.connect(lambda: self.delete_requested.emit(self.save_name))

        action_row.addWidget(self.btn_open_folder, 1)
        action_row.addWidget(self.btn_backup, 1)
        action_row.addWidget(self.btn_delete, 1)

        layout.addLayout(action_row)

        layout.addStretch()

    def _set_backup_btn_style(self, color_hex: str):
        self.btn_backup.setStyleSheet(
            f"QPushButton {{ background: {color_hex}; color: white; border: none; border-radius: 10px; font-size: 14px; font-weight: bold; }} QPushButton:hover {{ background: #059669; }} QPushButton:disabled {{ background: {color_hex}; color: rgba(255,255,255,0.8); border: none; }}")

    def load_save(
            self,
            save_name: str,
            icon_path: str,
            history: List[str],
            version_id: str = "",
            note: str = "",
            version_label: str = "未绑定版本",
    ):
        self.save_name = save_name
        self.name_label.setText(save_name)

        note_text = note.strip() or "无备注"
        self.meta_label.setText(f"绑定版本：{version_label}    ·    备注：{note_text}")
        apply_icon_to_label(self.icon_label, icon_path, 64)

        while self.combo_icon.count() > self.combo_icon.fixed_items_count:
            self.combo_icon.removeItem(self.combo_icon.fixed_items_count)
        self.combo_icon.load_history(history)

        if icon_path and not is_preset(icon_path):
            self.combo_icon.push_to_top(icon_path, is_history=True)
        elif icon_path:
            pass
        else:
            self.combo_icon.setCurrentIndex(0)

        self.set_backup_status("备份存档", True, "#10b981")

    def _on_icon_combo_activated(self, idx: int):
        text = self.combo_icon.itemText(idx)
        if text == "📁 自定义图片...":
            path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "选择图标", "", "Images (*.png *.jpg *.jpeg *.gif)")
            if path:
                self.combo_icon.push_to_top(path, is_history=True)
                apply_icon_to_label(self.icon_label, path, 64)
                self.icon_changed.emit(self.save_name, path)
        elif text == "🎨 打开预设图库...":
            dlg = PresetGalleryDialog("选择图标预设", PRESETS, self)
            if dlg.exec() == QtWidgets.QDialog.DialogCode.Accepted:
                preset = dlg.selected_preset
                apply_icon_to_label(self.icon_label, preset, 64)
                self.icon_changed.emit(self.save_name, preset)
        else:
            self.combo_icon.push_to_top(text, is_history=True)
            apply_icon_to_label(self.icon_label, text, 64)
            self.icon_changed.emit(self.save_name, text)

    def _open_save_folder(self):
        self.btn_open_folder.setEnabled(False)

        p = get_saves_directory() / self.save_name
        if p.exists(): open_in_file_explorer(p)

        QtCore.QTimer.singleShot(2000, lambda: self.btn_open_folder.setEnabled(True))

    def set_backup_status(self, text: str, enabled: bool, color_hex: str = "#10b981"):
        self.btn_backup.setText(text)
        self.btn_backup.setEnabled(enabled)
        self._set_backup_btn_style(color_hex)
        self.btn_backup.setCursor(
            QtCore.Qt.CursorShape.PointingHandCursor if enabled else QtCore.Qt.CursorShape.ForbiddenCursor)


class VersionOverviewPage(QtWidgets.QWidget):
    back_requested = QtCore.Signal()
    version_updated = QtCore.Signal(object)
    icon_history_removed = QtCore.Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.current_version: Optional[GameVersion] = None
        self._is_loading = False
        self._autosave_timer = QtCore.QTimer(self)
        self._autosave_timer.setSingleShot(True)
        self._autosave_timer.timeout.connect(self._save_meta)
        self._init_ui()

    def _init_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(16)

        top_nav = QtWidgets.QHBoxLayout()
        self.btn_back = QtWidgets.QPushButton("← 返回设置")
        self.btn_back.setFixedSize(85, 32)
        self.btn_back.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_back.setStyleSheet("""
            QPushButton {
                background-color: rgba(255, 255, 255, 0.7);
                border: 1px solid rgba(255, 255, 255, 0.6);
                border-radius: 12px;
                padding: 6px 8px;
                color: #222;
                font-weight: 500;
            }

            QPushButton:hover {
                background-color: rgba(255, 255, 255, 0.8);
            }

            QPushButton:pressed {
                background-color: rgba(255, 255, 255, 0.5);
            }
        """)

        self.btn_back.clicked.connect(self.back_requested.emit)
        top_nav.addWidget(self.btn_back)
        top_nav.addSpacing(0)

        self.title_label = QtWidgets.QLabel("📝 版本概览")
        self.title_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.title_label.setFixedHeight(36)
        self.title_label.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Maximum,
            QtWidgets.QSizePolicy.Policy.Fixed
        )
        self.title_label.setStyleSheet("""
             QLabel {
                 background: rgba(255, 255, 255, 0.8);
                 border-radius: 12px;
                 padding: 6px 16px;
                 font-size: 15px;
                 font-weight: 600;
                 color: #374151;
                 border: 1px solid rgba(0, 0, 0, 0.06);
             }
         """)

        top_nav.addWidget(self.title_label)
        top_nav.addStretch()

        layout.addLayout(top_nav)

        # ================= 预览卡片 =================
        self.preview_card = VersionPreviewCard()
        layout.addWidget(self.preview_card)

        # ================= 表单卡片 =================
        form_card = QtWidgets.QFrame()
        form_card.setObjectName("formCard")
        form_card.setStyleSheet("""
             QFrame#formCard {
                 background: rgba(255, 255, 255, 0.6);
                 border-radius: 16px;
                 border: 1px solid rgba(0, 0, 0, 0.06);
             }
         """)

        form_layout_wrapper = QtWidgets.QVBoxLayout(form_card)
        form_layout_wrapper.setContentsMargins(16, 16, 16, 16)
        form_layout_wrapper.setSpacing(10)

        section_title = QtWidgets.QLabel("基本信息")
        section_title.setStyleSheet("""
             font-size: 14px;
             font-weight: 600;
             color: #1F2937;
         """)
        form_layout_wrapper.addWidget(section_title)

        form = QtWidgets.QFormLayout()
        form.setVerticalSpacing(14)
        form.setHorizontalSpacing(12)
        form.setLabelAlignment(QtCore.Qt.AlignmentFlag.AlignLeft)
        form_layout_wrapper.addLayout(form)

        # ================= 统一输入样式 =================
        common_input_style = """
             QLineEdit, QTextEdit, QComboBox {
                 background: rgba(255, 255, 255, 0.85);
                 border: 1px solid rgba(0, 0, 0, 0.08);
                 border-radius: 10px;
                 padding: 6px 10px;
                 font-size: 13px;
                 color: #374151;
             }

             QLineEdit:hover, QTextEdit:hover, QComboBox:hover {
                 border: 1px solid rgba(43, 123, 228, 0.4);
             }

             QLineEdit:focus, QTextEdit:focus, QComboBox:focus {
                 border: 1px solid #2B7BE4;
                 background: rgba(255, 255, 255, 0.95);
             }
         """

        # ================= 输入项 =================
        self.inp_name = QtWidgets.QLineEdit()
        self.inp_name.setFixedHeight(34)
        self.inp_name.setStyleSheet(common_input_style)
        self.inp_name.textChanged.connect(self._on_live_update)
        self.inp_name.textChanged.connect(self._schedule_autosave)

        self.inp_note = QtWidgets.QTextEdit()
        self.inp_note.setFixedHeight(80)
        self.inp_note.setStyleSheet(common_input_style)
        self.inp_note.textChanged.connect(self._schedule_autosave)

        self.combo_icon = HistoryComboBox()
        self.combo_icon.setFixedHeight(34)

        self.combo_icon.add_fixed_items(["📁 自定义图片...", "🎨 打开预设图库..."])
        self.combo_icon.item_removed.connect(self.icon_history_removed.emit)
        self.combo_icon.activated.connect(self._on_icon_combo_activated)

        # ================= Label 样式 =================
        label_style = """
             QLabel {
                 color: #272320;
                 font-size: 13px;
                 font-weight: 550;
             }
         """
        self.setStyleSheet(self.styleSheet() + label_style)

        # ================= 表单填充 =================
        form.addRow("名称", self.inp_name)
        form.addRow("备注", self.inp_note)
        form.addRow("图标", self.combo_icon)

        layout.addWidget(form_card)
        layout.addStretch()

    def set_history(self, history: List[str]):
        while self.combo_icon.count() > self.combo_icon.fixed_items_count:
            self.combo_icon.removeItem(self.combo_icon.fixed_items_count)
        self.combo_icon.load_history(history)

    def load_version(self, version: GameVersion):
        self._is_loading = True
        self.current_version = version
        self.preview_card.update_version(version)

        if version:
            self.inp_name.setText(version.name)
            self.inp_note.setText(version.note)

            if version.icon_path and not is_preset(version.icon_path):
                self.combo_icon.push_to_top(version.icon_path, is_history=True)
            elif version.icon_path:
                pass
            else:
                self.combo_icon.setCurrentIndex(0)

            is_editable = True or version.is_modpack
            self.inp_name.setEnabled(is_editable)
            self.inp_note.setEnabled(is_editable)
            self.combo_icon.setEnabled(is_editable)
            # self.save_state.setText("自动保存已启用" if is_editable else "当前版本不可编辑")
            # self.save_state.setStyleSheet(
            #     "padding: 4px 10px; border-radius: 999px; background: #E0F2FE; color: #0369A1; font-size: 12px; font-weight: 700;" if is_editable
            #     else "padding: 4px 10px; border-radius: 999px; background: #F3F4F6; color: #6B7280; font-size: 12px; font-weight: 700;"
            # )

        self._is_loading = False

    def _schedule_autosave(self, icon_path: str = None):
        # if self._is_loading or not self.current_version or not self.current_version.is_modpack:
        if self._is_loading or not self.current_version:
            return
        # self.save_state.setText("待自动保存...")
        # self.save_state.setStyleSheet(
        #     "padding: 4px 10px; border-radius: 999px; background: #FEF3C7; color: #B45309; font-size: 12px; font-weight: 700;")
        self._autosave_timer.start(350)

    def _on_live_update(self):
        if self.current_version:
            self.preview_card.title_label.setText(self.inp_name.text() or self.current_version.name)

    def _on_icon_combo_activated(self, idx: int):
        text = self.combo_icon.itemText(idx)
        if text == "📁 自定义图片...":
            path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "选择图标", "", "Images (*.png *.jpg *.jpeg *.gif)")
            # dlg = QtWidgets.QFileDialog(self, "选择图标")
            # dlg.setFileMode(QtWidgets.QFileDialog.FileMode.ExistingFile)
            # dlg.setNameFilter("Images (*.png *.jpg *.jpeg *.gif)")
            # dlg.setOption(QtWidgets.QFileDialog.Option.DontUseNativeDialog, True)
            if path:
                self.combo_icon.push_to_top(path, is_history=True)
                apply_icon_to_label(self.preview_card.icon_label, path, 64,
                                    self.current_version.is_modpack if self.current_version else False)
                self._save_icon(path)
        elif text == "🎨 打开预设图库...":
            dlg = PresetGalleryDialog("选择图标预设", PRESETS, self)
            if dlg.exec() == QtWidgets.QDialog.DialogCode.Accepted:
                preset = dlg.selected_preset
                apply_icon_to_label(self.preview_card.icon_label, preset, 64,
                                    self.current_version.is_modpack if self.current_version else False)
                self._save_icon(preset)
        else:
            self.combo_icon.push_to_top(text, is_history=True)
            apply_icon_to_label(self.preview_card.icon_label, text, 64,
                                self.current_version.is_modpack if self.current_version else False)
            self._save_icon(text)

    def _save_meta(self):
        # if not self.current_version or not self.current_version.is_modpack:
        if not self.current_version:
            return

        self.current_version.name = self.inp_name.text()
        self.current_version.note = self.inp_note.toPlainText()

        self.current_version.save_modpack_meta()
        # self.save_state.setText("已自动保存")
        # self.save_state.setStyleSheet(
        #     "padding: 4px 10px; border-radius: 999px; background: #DCFCE7; color: #166534; font-size: 12px; font-weight: 700;")
        self.version_updated.emit(self.current_version)

    def _save_icon(self, icon_path: str = None):
        if not self.current_version:
            return
        current_icon = icon_path or self.combo_icon.currentText()
        if is_preset(current_icon):
            current_icon = str(PRESET_BACKGROUNDS_PATHS.get(get_preset_name(current_icon)))
        self.current_version.icon_path = current_icon
        self.current_version.save_modpack_meta()
        self.version_updated.emit(self.current_version)


class ConfigConflictDialog(QtWidgets.QDialog):
    def __init__(self, mod_name: str, parent=None):
        super().__init__(parent)
        self.setWindowTitle("检测到已存在配置")
        self.setModal(True)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Dialog
            | QtCore.Qt.WindowType.FramelessWindowHint
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose, True)

        self._choice = "cancel"

        root = QtWidgets.QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)

        card = QtWidgets.QFrame(self)
        card.setObjectName("conflictCard")
        card.setStyleSheet("""
            QFrame#conflictCard {
                background: rgba(255, 255, 255, 0.98);
                border: 1px solid rgba(15, 23, 42, 0.08);
                border-radius: 20px;
            }
            QLabel#titleLabel {
                color: #0F172A;
                font-size: 18px;
                font-weight: 800;
            }
            QLabel#msgLabel {
                color: #475569;
                font-size: 13px;
                line-height: 1.6;
            }
            QPushButton {
                border: none;
                border-radius: 12px;
                padding: 10px 16px;
                font-size: 13px;
                font-weight: 700;
                min-width: 88px;
            }
            QPushButton:hover { transform: translateY(-1px); }
        """)

        card_layout = QtWidgets.QVBoxLayout(card)
        card_layout.setContentsMargins(22, 20, 22, 20)
        card_layout.setSpacing(14)

        title = QtWidgets.QLabel(f"<b>{mod_name}</b> 已存在", card)
        title.setObjectName("titleLabel")

        msg = QtWidgets.QLabel(
            f"已存在同名 / 同 ID 模组。请选择处理方式：<br>"
            "“合并” 会保留当前配置并补充新版本字段；<br>"
            "“覆盖” 会直接使用压缩包里的完整文件。", card
        )
        msg.setObjectName("msgLabel")
        msg.setWordWrap(True)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.setSpacing(10)
        btn_row.addStretch()

        btn_merge = QtWidgets.QPushButton("合并", card)
        btn_overwrite = QtWidgets.QPushButton("覆盖", card)
        btn_cancel = QtWidgets.QPushButton("取消", card)

        btn_merge.setStyleSheet(
            "QPushButton { background: #2563EB; color: white; } QPushButton:hover { background: #1D4ED8; }")
        btn_overwrite.setStyleSheet(
            "QPushButton { background: #F59E0B; color: white; } QPushButton:hover { background: #D97706; }")
        btn_cancel.setStyleSheet(
            "QPushButton { background: #F1F5F9; color: #334155; } QPushButton:hover { background: #E2E8F0; }")

        btn_merge.clicked.connect(lambda: self._finish("merge"))
        btn_overwrite.clicked.connect(lambda: self._finish("overwrite"))
        btn_cancel.clicked.connect(lambda: self._finish("cancel"))

        btn_row.addWidget(btn_merge)
        btn_row.addWidget(btn_overwrite)
        btn_row.addWidget(btn_cancel)

        card_layout.addWidget(title)
        card_layout.addWidget(msg)
        card_layout.addStretch(1)
        card_layout.addLayout(btn_row)
        root.addWidget(card)

    def _finish(self, choice: str):
        self._choice = choice
        self.accept()

    @property
    def choice(self) -> str:
        return self._choice


class TipBubble(QtWidgets.QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)

        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            | QtCore.Qt.WindowType.Tool
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_ShowWithoutActivating)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)

        self.label = QtWidgets.QLabel()
        self.label.setWordWrap(False)  # ✅ 防止超宽
        self.label.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Maximum,
            QtWidgets.QSizePolicy.Policy.Preferred
        )
        self.label.setMaximumWidth(1024)  # ✅ 限制最大宽度，避免撑出 layout

        self.label.setStyleSheet("""
            background: rgba(0, 0, 0, 0.75);
            color: white;
            padding: 12px 20px;
            border-radius: 8px;
            font-size: 13px;
        """)
        self.label.setTextFormat(QtCore.Qt.TextFormat.RichText)

        layout.addWidget(self.label)

        # 透明度动画
        self.opacity_effect = QtWidgets.QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self.opacity_effect)
        self.opacity_effect.setOpacity(0)

        self.anim = QtCore.QPropertyAnimation(self.opacity_effect, b"opacity")
        self.anim.setDuration(220)

        self.hide_timer = QtCore.QTimer(self)
        self.hide_timer.setSingleShot(True)
        self.hide_timer.timeout.connect(self.fade_out)

        self.anim.finished.connect(self._on_anim_finished)

        self._closing = False

    def show_tip(
            self,
            text: str,
            anchor_pos: QtCore.QPoint,
            distance: int = 24,
            direction: str = "top",  # top / bottom / left / right
            duration: int = 3000,
    ):
        """
        anchor_pos: 图片中心点（global）
        distance: 与中心点的距离
        direction: 出现方向
        """

        self._closing = False

        self.label.setText(text)
        self.label.adjustSize()  # ✅ 根据内容调整大小
        self.adjustSize()

        pos = self._calc_position(anchor_pos, distance, direction)
        # pos = self._clamp_to_screen(pos)  # ✅ 防止出屏

        self.move(pos)
        self.show()
        self.raise_()

        # fade in
        self.anim.stop()
        self.anim.setStartValue(self.opacity_effect.opacity())
        self.anim.setEndValue(1)
        self.anim.setEasingCurve(QtCore.QEasingCurve.Type.OutCubic)  # ✅ 缓出效果
        self.anim.start()

        self.hide_timer.start(duration)

    def _calc_position(self, anchor, distance, direction):
        w, h = self.width(), self.height()

        if direction == "top":
            return QtCore.QPoint(anchor.x() - w // 2, anchor.y() - h - distance)
        elif direction == "bottom":
            return QtCore.QPoint(anchor.x() - w // 2, anchor.y() + distance)
        elif direction == "left":
            return QtCore.QPoint(anchor.x() - w - distance, anchor.y() - h // 2)
        elif direction == "right":
            return QtCore.QPoint(anchor.x() + distance, anchor.y() - h // 2)

        return anchor

    def _clamp_to_screen(self, pos: QtCore.QPoint) -> QtCore.QPoint:
        """防止气泡跑出屏幕"""
        screen = QtGui.QGuiApplication.primaryScreen().availableGeometry()

        x = max(screen.left(), min(pos.x(), screen.right() - self.width()))
        y = max(screen.top(), min(pos.y(), screen.bottom() - self.height()))

        return QtCore.QPoint(x, y)

    def fade_out(self):
        self._closing = True
        self.anim.stop()
        self.anim.setStartValue(self.opacity_effect.opacity())
        self.anim.setEndValue(0)
        self.anim.setEasingCurve(QtCore.QEasingCurve.Type.InCubic)  # ✅ 缓入效果
        self.anim.start()

    def _on_anim_finished(self):
        # ✅ 只在 fade_out 后隐藏（避免重复 connect 导致 bug）
        if self._closing:
            self.hide()


class ClickableLabel(QtWidgets.QLabel):
    clicked = QtCore.Signal()

    def mouseReleaseEvent(self, ev):
        if ev.button() == QtCore.Qt.MouseButton.LeftButton: self.clicked.emit()
        super().mouseReleaseEvent(ev)


class ApiInputDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, default_text="", hint=""):
        super().__init__(parent)
        # ✅ 无边框 + 透明背景
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint | QtCore.Qt.WindowType.Dialog
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)

        self.resize(400, 180)

        # 主容器（圆角卡片）
        container = QtWidgets.QFrame(self)
        container.setObjectName("container")
        container.setGeometry(0, 0, 400, 180)

        layout = QtWidgets.QVBoxLayout(container)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(15)

        # 标题（伪标题栏）
        title = QtWidgets.QLabel("🔑 输入 API Key")
        title.setStyleSheet("font-size:16px;font-weight:bold;")
        layout.addWidget(title)

        # 输入框
        self.input = QtWidgets.QLineEdit()
        self.input.setPlaceholderText(hint)
        self.input.setText(default_text)
        self.input.setMinimumHeight(36)
        layout.addWidget(self.input)

        # 按钮区
        btn_layout = QtWidgets.QHBoxLayout()
        btn_layout.addStretch()

        self.btn_cancel = QtWidgets.QPushButton("取消")
        self.btn_cancel.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

        self.btn_ok = QtWidgets.QPushButton("保存")
        self.btn_ok.setObjectName("btn_ok")
        self.btn_ok.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

        btn_layout.addWidget(self.btn_cancel)
        btn_layout.addWidget(self.btn_ok)

        layout.addLayout(btn_layout)

        # 事件
        self.btn_cancel.clicked.connect(self.reject)
        self.btn_ok.clicked.connect(self.accept)

        self.input.returnPressed.connect(self.accept)
        # 设置保存按钮为默认按钮
        self.btn_ok.setDefault(True)
        self.btn_ok.setAutoDefault(True)

        self.setStyleSheet("""
            QFrame#container {
                background-color: rgba(255, 255, 255, 252);
                border-radius: 12px;
                border: 2px solid #ddd;
            }
            QLineEdit {
                border: 1px solid #ccc;
                border-radius: 8px;
                padding: 6px 10px;
                background: #f9f9f9;
                color: #333;
            }
            QLineEdit:focus {
                border: 1px solid #0078d4;
                background: #ffffff;
            }
            QPushButton {
                border-radius: 8px;
                padding: 6px 14px;
                background: #f0f0f0;
                color: #333;
                border: 1px solid #ccc;
            }
            QPushButton:hover {
                background: #e6e6e6;
            }
            QPushButton#btn_ok {
                background: #2B7BE4;
                color: white;
                border: none;
            }
            QPushButton#btn_ok:hover {
                background: #3C88EA;
            }
        """)

    def get_value(self):
        return self.input.text().strip()


class GameRootSelectDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, is_has_version=False):
        super().__init__(parent)
        self.selected_root: Optional[Path] = None
        self.setWindowFlags(QtCore.Qt.WindowType.FramelessWindowHint | QtCore.Qt.WindowType.Dialog)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.resize(520, 220)

        container = QtWidgets.QFrame(self)
        container.setObjectName("container")
        container.setGeometry(0, 0, 520, 220)

        layout = QtWidgets.QVBoxLayout(container)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)

        title = QtWidgets.QLabel("🎮 选择游戏根目录")
        title.setStyleSheet("font-size:16px;font-weight:bold;")
        subtitle = QtWidgets.QLabel(r"请选择包含 Stardew Valley 的文件夹，例如 D:\...\Steam\steamapps\common")
        subtitle.setWordWrap(True)
        subtitle.setStyleSheet("color:#6b7280;font-size:13px;")
        layout.addWidget(title)
        layout.addWidget(subtitle)

        # 只保留路径输入框
        self.path_edit = QtWidgets.QLineEdit()
        self.path_edit.setReadOnly(True)
        self.path_edit.setPlaceholderText(f"点击这里选择游戏目录{' (当前已检测到游戏)' if is_has_version else ''}")
        self.path_edit.setMinimumHeight(36)
        self.path_edit.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.path_edit.mousePressEvent = self._browse  # 点击时调用浏览
        layout.addWidget(self.path_edit)

        btn_layout = QtWidgets.QHBoxLayout()
        btn_layout.addStretch()
        self.btn_ok = QtWidgets.QPushButton("确定")
        self.btn_ok.setObjectName("btn_ok")
        self.btn_ok.clicked.connect(self._accept_selected)
        self.btn_ok.setDefault(True)

        self.btn_cancel = QtWidgets.QPushButton("取消")
        self.btn_cancel.clicked.connect(self.reject)
        btn_layout.addWidget(self.btn_cancel)
        btn_layout.addWidget(self.btn_ok)
        layout.addLayout(btn_layout)

        self.setStyleSheet("""
            QFrame#container {
                background-color: rgba(255, 255, 255, 252);
                border-radius: 12px;
                border: 2px solid #ddd;
            }
            QLineEdit {
                border: 1px solid #ccc;
                border-radius: 8px;
                padding: 6px 10px;
                background: #f9f9f9;
                color: #333;
            }
            QLineEdit:hover {
                background: #f0f0f0;
            }
            QPushButton {
                border-radius: 8px;
                padding: 6px 14px;
                background: #f0f0f0;
                color: #333;
                border: 1px solid #ccc;
            }
            QPushButton:hover {
                background: #e6e6e6;
            }
            QPushButton#btn_ok {
                background: #2B7BE4;
                color: white;
                border: none;
            }
            QPushButton#btn_ok:hover {
                background: #3C88EA;
            }
        """)

    def _browse(self, event=None):
        root = QtWidgets.QFileDialog.getExistingDirectory(
            self,
            "选择游戏根目录",
            str(BASE_DIR.parent),
            QtWidgets.QFileDialog.Option.ShowDirsOnly
        )
        if not root:
            return
        self.selected_root = Path(root).resolve()
        self.path_edit.setText(str(self.selected_root))

    def _accept_selected(self):
        if self.selected_root and self.selected_root.exists():
            self.accept()
        else:
            QtWidgets.QMessageBox.warning(self, "提示", "请先选择一个有效的游戏目录。")

    def get_value(self) -> Optional[Path]:
        return self.selected_root


class _CenteredMediaLabel(QtWidgets.QWidget):
    """始终把静态图 / GIF 居中绘制到自身矩形中。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._pixmap: Optional[QtGui.QPixmap] = None
        self._movie: Optional[QtGui.QMovie] = None
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)

    def set_centered_pixmap(self, pixmap: Optional[QtGui.QPixmap]):
        if self._movie is not None:
            try:
                self._movie.frameChanged.disconnect(self.update)
            except Exception:
                pass
        self._movie = None
        self._pixmap = pixmap if pixmap and not pixmap.isNull() else None
        self.update()

    def set_centered_movie(self, movie: Optional[QtGui.QMovie]):
        if self._movie is not None:
            try:
                self._movie.frameChanged.disconnect(self.update)
            except Exception:
                pass

        self._movie = movie
        self._pixmap = None

        if self._movie is not None:
            self._movie.frameChanged.connect(self.update)

        self.update()

    def paintEvent(self, event: QtGui.QPaintEvent):
        painter = QtGui.QPainter(self)
        painter.setRenderHint(QtGui.QPainter.RenderHint.SmoothPixmapTransform, True)

        pm = None
        if self._movie is not None:
            pm = self._movie.currentPixmap()
        elif self._pixmap is not None:
            pm = self._pixmap

        if pm is not None and not pm.isNull():
            x = (self.width() - pm.width()) // 2
            y = (self.height() - pm.height()) // 2
            painter.drawPixmap(x, y, pm)


class GifWidget(QtWidgets.QWidget):
    center_gif_clicked = QtCore.Signal(str)

    def __init__(
            self,
            default_path: str | Path,
            clicked_path: Optional[str | Path] = None,
            overloaded_path: Optional[str | Path] = None,
            default_size: int = 128,  # 现在表示“宽度”
            clicked_size: int = 128,
            overloaded_size: int = 128,
            click_area_size: int = 128,
            parent=None,
    ):
        super().__init__(parent)

        self._default_path = str(default_path)
        self._clicked_path = str(clicked_path)
        self._overloaded_path = str(overloaded_path)

        self._default_size = max(1, int(default_size))
        self._clicked_size = max(1, int(clicked_size))
        self._overloaded_size = max(1, int(overloaded_size))
        self._click_area_size = max(1, int(click_area_size))

        self._default_movie = None
        self._clicked_movie = None
        self._overloaded_movie = None

        self._click_timestamps = deque()
        self._overload_window = 3
        self._overload_threshold = 10
        self._overload_active = False

        self._clicked_conn = None
        self._overloaded_conn = None

        self._restore_timer = QtCore.QTimer(self)
        self._restore_timer.setSingleShot(True)
        self._restore_timer.timeout.connect(self._end_overload_wait)

        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Fixed,
            QtWidgets.QSizePolicy.Policy.Fixed,
        )

        root = QtWidgets.QGridLayout(self)
        root.setContentsMargins(0, 0, 0, 0)

        self._image_layer = QtWidgets.QWidget(self)
        self._image_layer.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self._image_layer.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)

        layout = QtWidgets.QStackedLayout(self._image_layer)
        layout.setStackingMode(QtWidgets.QStackedLayout.StackingMode.StackAll)
        layout.setContentsMargins(0, 0, 0, 0)

        self._default_label = _CenteredMediaLabel()
        self._clicked_label = _CenteredMediaLabel()
        self._overloaded_label = _CenteredMediaLabel()

        for lb in (self._default_label, self._clicked_label, self._overloaded_label):
            lb.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)

        layout.addWidget(self._default_label)
        layout.addWidget(self._clicked_label)
        layout.addWidget(self._overloaded_label)

        root.addWidget(self._image_layer, 0, 0)

        self._load_media()

    # ---------------- media ----------------

    def _exists(self, path: str) -> bool:
        return bool(path) and QtCore.QFile.exists(path)

    def _calc_scaled_size(self, path: str, target_width: int) -> QtCore.QSize:
        """根据原始比例计算缩放尺寸。通过 QImageReader 获取原始尺寸（适用于 GIF 和静态图）。"""
        try:
            reader = QtGui.QImageReader(path)
            original_size = reader.size()
        except Exception:
            original_size = QtCore.QSize()

        if not original_size.isValid() or original_size.width() <= 0:
            return QtCore.QSize(target_width, target_width)

        w = target_width
        h = max(1, int(original_size.height() * (w / original_size.width())))
        return QtCore.QSize(w, h)

    def _apply_media(self, label, path, width, auto_start=False):
        if not self._exists(path):
            label.set_centered_pixmap(None)
            return None, QtCore.QSize(0, 0)

        # GIF
        if path.lower().endswith(".gif"):
            movie = QtGui.QMovie(path, parent=self)
            size = self._calc_scaled_size(path, width)
            movie.setScaledSize(size)
            label.set_centered_movie(movie)

            if auto_start:
                movie.start()
            else:
                movie.stop()

            return movie, size

        # 静态图
        pix = QtGui.QPixmap(path)
        if pix.isNull():
            label.set_centered_pixmap(None)
            return None, QtCore.QSize(0, 0)

        scaled = pix.scaled(
            width,
            width * 10,  # 给足高度空间
            QtCore.Qt.AspectRatioMode.KeepAspectRatio,
            QtCore.Qt.TransformationMode.SmoothTransformation,
        )
        label.set_centered_pixmap(scaled)
        return None, scaled.size()

    def _load_media(self):
        self._default_movie, s1 = self._apply_media(
            self._default_label, self._default_path, self._default_size, True
        )
        self._clicked_movie, s2 = self._apply_media(
            self._clicked_label, self._clicked_path, self._clicked_size
        )
        self._overloaded_movie, s3 = self._apply_media(
            self._overloaded_label, self._overloaded_path, self._overloaded_size
        )

        max_w = max(1, s1.width(), s2.width(), s3.width())
        max_h = max(1, s1.height(), s2.height(), s3.height())

        self.setFixedSize(max_w, max_h)
        self._image_layer.setFixedSize(max_w, max_h)

        for lb in (self._default_label, self._clicked_label, self._overloaded_label):
            lb.setFixedSize(max_w, max_h)

        self._show_only("default")

    # ---------------- playback ----------------

    def _disconnect(self, movie: QtGui.QMovie, attr_name):
        conn = getattr(self, attr_name)
        if conn:
            try:
                movie.frameChanged.disconnect(conn)
            except Exception:
                pass
            setattr(self, attr_name, None)

    def _play_loops(self, movie: QtGui.QMovie, label_name, conn_attr, lock_click=False, loops=1, restore_delay_ms=0):
        if not movie or loops <= 0:
            return

        self._disconnect(movie, conn_attr)
        self._show_only(label_name)

        movie.stop()
        try:
            movie.jumpToFrame(0)
        except Exception:
            pass

        frame_count = movie.frameCount()

        # ---------- fallback ----------
        if frame_count <= 0:
            started = False
            seen_non_zero = False
            loop_count = 0

            def on_frame(frame):
                nonlocal started, seen_non_zero, loop_count

                if not started:
                    if frame == 0:
                        started = True
                    return

                if frame > 0:
                    seen_non_zero = True
                    return

                if seen_non_zero:
                    loop_count += 1
                    seen_non_zero = False

                    if loop_count >= loops:
                        movie.stop()
                        self._disconnect(movie, conn_attr)
                        self._finish(lock_click, restore_delay_ms)

            movie.frameChanged.connect(on_frame)
            setattr(self, conn_attr, on_frame)
            movie.start()
            return

        # ---------- normal ----------
        last_frame = frame_count - 1
        loop_count = 0

        def on_frame(frame):
            nonlocal loop_count
            if frame == last_frame:
                loop_count += 1
                if loop_count >= loops:
                    print(f"stop {conn_attr}")
                    movie.stop()
                    self._disconnect(movie, conn_attr)
                    self._finish(lock_click, restore_delay_ms)

        movie.frameChanged.connect(on_frame)
        setattr(self, conn_attr, on_frame)

        movie.start()

    def _finish(self, lock_click, restore_delay_ms=0):
        if lock_click:
            if restore_delay_ms > 0:
                self._show_only("None")
                print("overload wait")
                self._restore_timer.stop()
                self._restore_timer.start(restore_delay_ms)
            else:
                self._end_overload_wait()
            return

        self._restore_default()

    def _end_overload_wait(self):
        self._restore_timer.stop()
        self._overload_active = False
        self._restore_default()

    def _restore_default(self):
        if not self._default_movie:
            return

        try:
            self._default_movie.stop()
            self._default_movie.jumpToFrame(0)
        except Exception:
            pass

        self._default_movie.start()
        self._show_only("default")

    def _show_only(self, which):
        self._default_label.setVisible(which == "default")
        self._clicked_label.setVisible(which == "clicked")
        self._overloaded_label.setVisible(which == "overloaded")

    # ---------------- logic ----------------

    def _play_clicked(self):
        popup_sound.play()
        self._play_loops(
            self._clicked_movie,
            "clicked",
            "_clicked_conn",
            loops=1,
        )

    def _play_overloaded(self):
        self._overload_active = True
        self._clicked_movie.stop()
        # self._disconnect(self._clicked_movie, "_clicked_conn")
        if IS_MY_BIRTHDAY and mc_firework_sound is not None:
            mc_firework_sound.play()
        else:
            QtCore.QTimer.singleShot(60, tnt_sound.play)
        self._play_loops(
            self._overloaded_movie,
            "overloaded",
            "_overloaded_conn",
            lock_click=True,
            loops=1,
            restore_delay_ms=0,
        )

    def _on_click(self):
        if self._overload_active:
            return


        now = time.monotonic()
        self._click_timestamps.append(now)

        cutoff = now - self._overload_window
        while self._click_timestamps and self._click_timestamps[0] < cutoff:
            self._click_timestamps.popleft()

        if (
                len(self._click_timestamps) >= self._overload_threshold
                and self._overloaded_movie
        ):
            self._click_timestamps.clear()
            self._play_overloaded()
            self.center_gif_clicked.emit("overloaded")
            return

        if self._clicked_movie:
            self._play_clicked()
            self.center_gif_clicked.emit("clicked")

    # ---------------- event ----------------

    def mouseReleaseEvent(self, e: QtGui.QMouseEvent):
        if e.button() == QtCore.Qt.MouseButton.LeftButton:
            self._on_click()
            return
        super().mouseReleaseEvent(e)


class LeftPane(QtWidgets.QWidget):
    version_selected = QtCore.Signal(GameVersion)
    open_settings = QtCore.Signal()
    open_version_selector = QtCore.Signal()
    TIPS = [
        "你知道吗？<b>星露谷</b>中鸡可以孵出虚空鸡哦",
        "按住 <b>Shift</b> 点击可以快速转移物品",
        "记得每天看电视，了解明天的天气和运气",
        "使用 <b>Mod</b> 前记得备份存档，以防万一",
        "<span style='color: #FFD700;'>金星</span>品质的农作物能卖更好的价钱",
        "升级到 <b>铜镐</b> 后就能敲开矿洞里的大石头",
        "在社区中心完成任务可以解锁新功能，比如温室修复",
        "雨天是捕捉稀有鱼类的好机会，比如鲟鱼",
        "种植 <b>古代种子</b> 可以收获古代水果，是高利润作物",
        "每天和村民对话、送礼物能快速提升好感度，解锁剧情和奖励",
        "在矿洞第 <b>40</b> 层后会出现大量铁矿，第 <b>80</b> 层后则有金矿",
        "冬天虽然不能种田，但可以专注于钓鱼、采矿和提升技能",
        "<b>升级背包</b>到 36 格能大幅提升效率，前期优先投资",
        "在农场放置<b>蜂箱</b>，种花可以产出对应花蜜的蜂蜜",
        "用<b>洒水器</b>可以自动浇水，高级洒水器能覆盖更大范围",
        "在<b>温室</b>里种植作物可以全年收获，不受季节限制",
        "完成社区中心的鱼缸任务后，可以解锁池塘养殖功能",
        "在矿洞遇到电梯层时，记得下次可以直接传送到该层",
        "刘易斯的紫色短裤可以在<b>秋季展览</b>中展示，获得隐藏对话和额外分数",
        "<b>窃贼戒指</b>能提高怪物掉落率，是刷稀有材料的神器",
        "<b>黄金南瓜</b>是万灵节奖励，几乎所有村民都喜欢，是通用送礼神器",
        "<b>咖啡</b>能提升移动速度，也是多个角色的喜爱礼物",
        "在温室种植<b>古代水果</b>可以全年收获，是最稳定的高利润来源",
        "与莱纳斯好感度达到 4 心后会赠送<b>万能鱼饵</b>配方，使用后有概率一次钓到两条鱼",
    ]

    tip_times = 0
    last_tip_index = None
    is_triggerd_happy_birthday = False

    def __init__(self, fixed_width: int = 240, parent=None, main_window=None):
        super().__init__(parent)
        self.fixed_width = fixed_width
        self.main_window = main_window
        self.setFixedWidth(self.fixed_width)
        self._selected_version: Optional[GameVersion] = None
        self._init_ui()
        self.tip_bubble = TipBubble(self.main_window)

    def _init_ui(self):
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setObjectName("leftPane")
        self.setStyleSheet(
            "#leftPane { background: rgba(255, 255, 255, 0.5); border-right: 1px solid rgba(0,0,0,0.06); }"
        )

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(10)

        self.versions_scroll = SmoothScrollArea()
        self.versions_scroll.setWidgetResizable(True)
        self.versions_scroll.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.versions_scroll.setSizeAdjustPolicy(
            QtWidgets.QAbstractScrollArea.SizeAdjustPolicy.AdjustIgnored
        )

        self.versions_container = QtWidgets.QWidget()
        self.versions_container.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Expanding,
            QtWidgets.QSizePolicy.Policy.MinimumExpanding,
        )

        self.versions_layout = QtWidgets.QVBoxLayout(self.versions_container)
        self.versions_layout.setContentsMargins(0, 0, 0, 0)
        self.versions_layout.setSpacing(0)

        # 中间 GIF 容器
        self.center_gif_container = QtWidgets.QWidget()
        cg_layout = QtWidgets.QVBoxLayout(self.center_gif_container)
        cg_layout.setContentsMargins(0, 0, 0, 0)
        cg_layout.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)

        # 默认 GIF / 点击后 GIF
        default_gif = IMAGES_PATH / "xd_usual.gif"
        clicked_gif = IMAGES_PATH / "xd_clicked.gif"
        overloaded_gif = (IMAGES_PATH / "TNT_explosion_zoom2x.gif") if not IS_MY_BIRTHDAY else (IMAGES_PATH / "minecraft_firework.gif")

        # default_gif = r"resources\images\test5.gif"
        # clicked_gif = r"resources\images\test6.gif"
        # overloaded_gif = r"resources\images\test3.gif"

        if not Path(clicked_gif).exists():
            clicked_gif = default_gif

        self.center_gif = GifWidget(
            default_path=default_gif,
            clicked_path=clicked_gif,
            overloaded_path=overloaded_gif,
            default_size=240,
            clicked_size=240,
            overloaded_size=240,
            click_area_size=100,
        )

        self.center_gif.center_gif_clicked.connect(self._show_random_tip)
        cg_layout.addWidget(self.center_gif, 0, QtCore.Qt.AlignmentFlag.AlignCenter)

        self.versions_layout.addStretch()
        self.versions_layout.addWidget(self.center_gif_container)
        self.versions_layout.addStretch()

        self.versions_scroll.setWidget(self.versions_container)
        layout.addWidget(self.versions_scroll, 1)

        bottom_widget = QtWidgets.QWidget()
        bottom_layout = QtWidgets.QVBoxLayout(bottom_widget)
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        bottom_layout.setSpacing(8)

        self.btn_launch = QtWidgets.QPushButton()
        self.btn_launch.setFixedHeight(50)
        self.btn_launch.setStyleSheet(
            "QPushButton { border: 2px solid #2B7BE4; color: #2B7BE4; background: white; border-radius: 8px; font-weight:700; } "
            "QPushButton:pressed { background: rgba(43,123,228,0.06); }"
        )
        self.btn_launch.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        launch_layout = QtWidgets.QVBoxLayout(self.btn_launch)
        launch_layout.setContentsMargins(0, 0, 0, 0)
        launch_layout.setSpacing(0)
        launch_layout.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)

        self.launch_label_main = QtWidgets.QLabel("启动游戏")
        self.launch_label_main.setStyleSheet(
            "color:#2B7BE4; font-weight:700; font-size:15px; background: transparent;"
        )
        self.launch_label_main.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.launch_label_sub = QtWidgets.QLabel("当前版本: 未选择")
        self.launch_label_sub.setStyleSheet("color:#888; font-size:11px; background: transparent;")
        self.launch_label_sub.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        launch_layout.addWidget(self.launch_label_main)
        launch_layout.addWidget(self.launch_label_sub)
        bottom_layout.addWidget(self.btn_launch)

        half_row = QtWidgets.QWidget()
        half_layout = QtWidgets.QHBoxLayout(half_row)
        half_layout.setContentsMargins(0, 0, 0, 0)
        half_layout.setSpacing(8)
        self.btn_version_select = QtWidgets.QPushButton("版本选择")
        self.btn_settings = QtWidgets.QPushButton("设置与管理")
        for b in (self.btn_version_select, self.btn_settings):
            b.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
            b.setFixedHeight(36)
            b.setStyleSheet(
                "QPushButton { background: #F6F8FA; border: 1px solid rgba(0,0,0,0.06); border-radius: 8px; font-size:13px; } "
                "QPushButton:pressed { background: #EEF3FF; }"
            )
            half_layout.addWidget(b)
        bottom_layout.addWidget(half_row)
        layout.addWidget(bottom_widget)

        self.btn_settings.clicked.connect(self.open_settings.emit)
        self.btn_version_select.clicked.connect(self.open_version_selector.emit)
        self.btn_launch.clicked.connect(self._on_launch_clicked)

    def _select_tip(self):
        def try_get_birthday_tip() -> str:
            dif_hours = count_hours(b_event.datetime)
            if not (dif_hours <= 200):
                return ""

            if dif_hours <= 0:
                if not self.is_triggerd_happy_birthday:
                    self.is_triggerd_happy_birthday = True
                    return "🧁 生日快乐！！！🎂🎉✨"
                else:
                    tips_list = [
                        "🧁 许下美好愿望 🕯️🌟🌈",
                        "🧁 星光闪耀的夜晚 ✨⭐🌙",
                        "🧁 轻声唱起生日歌 🎶🎂",
                        "🧁 温柔的烛光摇曳 🕯️💫",
                        "🧁 Come on Everypony Smile Smile Smile! 🎉🌸",
                        "🧁 礼物承载着心意 🎁💖",
                        "🧁 气球缓缓升起 🎈🌤️",
                        "🧁 愿你被温柔环绕 🌷✨",
                        "🧁 朋友的陪伴最珍贵 🤝💞",
                        "🧁 心愿随风飘远 🌬️🌠"
                    ]
                    return random.choice(tips_list)

            return f"还有 {dif_hours} 小时..."

        def choice_tip():
            print("choice_tip")
            try:
                for _ in range(3):  # 最多尝试 3 次
                    idx = random.randrange(len(self.TIPS))
                    if idx != self.last_tip_index:
                        self.last_tip_index = idx
                        return self.TIPS[idx]

                def activate_overload():
                    self.center_gif._overload_active = False

                self.center_gif._overload_active = True
                QtCore.QTimer.singleShot(4000, activate_overload)
                return "你知道吗，触发这条tip的概率是0.0017361%......"
            except:
                return random.choice(self.TIPS)

        self.tip_times += 1
        if self.tip_times % 10 == 0:
            return try_get_birthday_tip() or choice_tip()

        return choice_tip()

    def _show_random_tip(self, gif_type=""):
        if gif_type == "overloaded" and IS_MY_BIRTHDAY:
            self.show_tip("🌟 你知道吗，今天是咱的生日！🎉🎇")
            return

        tip = self._select_tip()
        self.show_tip(tip)

    def show_tip(self, tip: str):
        # 以图片中心点为基准，向上偏移一定距离
        center_pos = self.center_gif.mapToGlobal(self.center_gif.rect().center())
        self.tip_bubble.show_tip(tip, center_pos, distance=180)

    def set_selected_version(self, version: Optional[GameVersion]):
        self._selected_version = version
        self.launch_label_sub.setText(version.name if version else "当前版本: 未选择")

    def _on_launch_clicked(self):
        if self._selected_version:
            self.version_selected.emit(self._selected_version)


class ModActionDialog(QtWidgets.QDialog):
    possible_clicked = QtCore.Signal()
    other_clicked = QtCore.Signal(str)  # 传回按钮文字，方便区分
    closed = QtCore.Signal()

    def __init__(self, parent=None, text="这里放提示文本"):
        super().__init__(parent)

        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint | QtCore.Qt.WindowType.Dialog
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.resize(460, 230)

        container = QtWidgets.QFrame(self)
        container.setObjectName("container")
        container.setGeometry(0, 0, 460, 230)

        layout = QtWidgets.QVBoxLayout(container)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)

        title = QtWidgets.QLabel("✨ 提示")
        title.setStyleSheet("font-size:16px;font-weight:bold;color:#111827;")
        layout.addWidget(title)

        self.text_label = QtWidgets.QLabel(text)
        self.text_label.setWordWrap(True)
        self.text_label.setStyleSheet("font-size:14px;color:#374151;")
        layout.addWidget(self.text_label)

        btn_layout = QtWidgets.QGridLayout()
        btn_layout.setHorizontalSpacing(6)
        btn_layout.setVerticalSpacing(6)

        self.btn_possible = self._make_btn("可能", primary=False)

        self.btn_yes = self._make_btn("是的", primary=True)
        self.btn_can = self._make_btn("可以", primary=True)
        self.btn_ok = self._make_btn("好的", primary=True)
        self.btn_come = self._make_btn("来吧", primary=True)
        self.btn_summon = self._make_btn("召唤", primary=True)

        # 2 行 3 列
        btn_layout.addWidget(self.btn_possible, 0, 0)
        btn_layout.addWidget(self.btn_yes, 0, 1)
        btn_layout.addWidget(self.btn_can, 0, 2)

        btn_layout.addWidget(self.btn_ok, 1, 0)
        btn_layout.addWidget(self.btn_come, 1, 1)
        btn_layout.addWidget(self.btn_summon, 1, 2)

        layout.addLayout(btn_layout)

        self.btn_possible.clicked.connect(self._on_possible)
        self.btn_yes.clicked.connect(lambda: self._on_other("是的"))
        self.btn_can.clicked.connect(lambda: self._on_other("可以"))
        self.btn_ok.clicked.connect(lambda: self._on_other("好的"))
        self.btn_come.clicked.connect(lambda: self._on_other("来吧"))
        self.btn_summon.clicked.connect(lambda: self._on_other("召唤"))

        self.setStyleSheet("""
            QFrame#container {
                background-color: rgba(255, 255, 255, 252);
                border-radius: 12px;
                border: 2px solid #ddd;
            }

            QLabel {
                color: #111827;
            }

            QPushButton {
                border-radius: 6px;
                padding: 2px 6px;
                background: #f0f0f0;
                color: #333;
                border: 1px solid #ccc;
                font-size: 12px;
                min-height: 28px;
            }

            QPushButton:hover {
                background: #e6e6e6;
            }

            QPushButton#btn_primary {
                background: #2B7BE4;
                color: white;
                border: none;
            }

            QPushButton#btn_primary:hover {
                background: #3C88EA;
            }

            QPushButton#btn_primary:pressed {
                background: #1F6FD6;
            }
        """)

    def _make_btn(self, text: str, primary: bool = False) -> QtWidgets.QPushButton:
        btn = QtWidgets.QPushButton(text)
        btn.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

        # 按钮缩小
        btn.setFixedSize(72, 30)

        if primary:
            btn.setObjectName("btn_primary")

        return btn

    def _on_possible(self):
        self.possible_clicked.emit()
        self.accept()

    def _on_other(self, text: str):
        self.other_clicked.emit(text)
        self.accept()

    def closeEvent(self, event: QtGui.QCloseEvent):
        self.closed.emit()
        super().closeEvent(event)


class RightPane(QtWidgets.QWidget):
    open_saves_requested = QtCore.Signal()
    open_mod_viewer_requested = QtCore.Signal()
    open_overview_requested = QtCore.Signal()
    bg_changed = QtCore.Signal(str)
    bg_history_removed = QtCore.Signal(str)
    version_updated = QtCore.Signal(object)
    show_add_api_dialog_requested = QtCore.Signal()
    show_add_game_root_requested = QtCore.Signal()

    mod_magic_possible_requested = QtCore.Signal()
    mod_magic_other_requested = QtCore.Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.current_version: Optional[GameVersion] = None
        self._init_ui()

    def _init_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(18, 18, 18, 18)
        self.content_area = QtWidgets.QStackedWidget()
        layout.addWidget(self.content_area)

        # 0. Empty
        empty = QtWidgets.QWidget()
        empty_layout = QtWidgets.QVBoxLayout(empty)
        lbl = QtWidgets.QLabel("")
        lbl.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        empty_layout.addWidget(lbl)
        self.content_area.addWidget(empty)

        # 1. Versions
        self.versions_page = SmoothScrollArea()
        self.versions_list_container = QtWidgets.QWidget()
        self.versions_list_layout = QtWidgets.QVBoxLayout(self.versions_list_container)
        self.versions_list_layout.addStretch()
        self.versions_page.setWidget(self.versions_list_container)
        self.content_area.addWidget(self.versions_page)

        # 2. Settings
        self.settings_page = QtWidgets.QWidget()
        s_layout = QtWidgets.QVBoxLayout(self.settings_page)

        grp_global = QtWidgets.QGroupBox("🌏 全局设置")
        glayout = QtWidgets.QVBoxLayout(grp_global)

        bg_layout = QtWidgets.QHBoxLayout()
        bg_layout.addWidget(QtWidgets.QLabel("🖼️ 背景图片:"))

        self.combo_bg = HistoryComboBox()
        self.combo_bg.add_fixed_items(["📁 自定义背景...", "🎨 打开预设图库..."])
        self.combo_bg.item_removed.connect(self.bg_history_removed.emit)
        self.combo_bg.activated.connect(self._on_bg_combo_activated)

        bg_layout.addWidget(self.combo_bg, 1)
        glayout.addLayout(bg_layout)

        self.btn_save_info = QtWidgets.QPushButton("💾 存档信息")
        self.btn_save_info.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self._style_settings_btn(self.btn_save_info)
        glayout.addWidget(self.btn_save_info)

        self.btn_add_api = QtWidgets.QPushButton("🔑 添加 API Key")
        self.btn_add_api.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self._style_settings_btn(self.btn_add_api)
        glayout.addWidget(self.btn_add_api)

        self.btn_add_game_root = QtWidgets.QPushButton("🎮 游戏路径")
        self.btn_add_game_root.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self._style_settings_btn(self.btn_add_game_root)
        glayout.addWidget(self.btn_add_game_root)

        self._style_groupbox(grp_global)
        s_layout.addWidget(grp_global)

        grp_version = QtWidgets.QGroupBox("📚 版本设置")
        vlayout = QtWidgets.QVBoxLayout(grp_version)

        self.current_ver_preview = VersionPreviewCard()
        vlayout.addWidget(self.current_ver_preview)

        self.btn_overview = QtWidgets.QPushButton("📝 版本概览")
        self.btn_overview.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_open_current_folder = QtWidgets.QPushButton("📁 主程序文件夹")
        self.btn_open_current_folder.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_open_mod_viewer = QtWidgets.QPushButton("🧩 Mod 管理")
        self.btn_open_mod_viewer.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        for b in (self.btn_overview, self.btn_open_current_folder, self.btn_open_mod_viewer):
            self._style_settings_btn(b)
            vlayout.addWidget(b)

        # ------- 这里是你要的新图片：Mod 管理下一行，居中 -------
        self.mod_magic_row = QtWidgets.QWidget()
        magic_row_layout = QtWidgets.QHBoxLayout(self.mod_magic_row)
        magic_row_layout.setContentsMargins(0, 8, 0, 0)
        magic_row_layout.addStretch()

        self.mod_magic_label = ClickableLabel()
        self.mod_magic_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.mod_magic_label.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.mod_magic_label.setFixedSize(72, 72)
        self.mod_magic_label.setStyleSheet("background: transparent;")
        self.mod_magic_label.clicked.connect(self._on_mod_magic_clicked)

        # 这里替换成你的图片路径
        self.mod_magic_icon_path = B_EVENT_PATH / "pink_cake.png"
        apply_icon_to_label(self.mod_magic_label, str(self.mod_magic_icon_path), 72)

        magic_row_layout.addWidget(self.mod_magic_label)
        magic_row_layout.addStretch()

        vlayout.addWidget(self.mod_magic_row)
        self.mod_magic_row.setVisible(b_event.is_triggered)  # 默认显示；需要隐藏时调用 hide_mod_magic_image()

        self._style_groupbox(grp_version)

        s_layout.addWidget(grp_version)
        s_layout.addStretch()
        self.content_area.addWidget(self.settings_page)

        # 3. Saves
        self.saves_page = QtWidgets.QWidget()
        saves_layout = QtWidgets.QVBoxLayout(self.saves_page)
        saves_layout.setContentsMargins(0, 0, 0, 0)
        top_save_nav = QtWidgets.QHBoxLayout()
        self.btn_back = QtWidgets.QPushButton("← 返回设置")
        self.btn_back.setFixedSize(85, 32)
        self.btn_back.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_back.setStyleSheet("""
            QPushButton {
                background-color: rgba(255, 255, 255, 0.7);
                border: 1px solid rgba(255, 255, 255, 0.6);
                border-radius: 12px;
                padding: 6px 8px;
                color: #222;
                font-weight: 500;
            }

            QPushButton:hover {
                background-color: rgba(255, 255, 255, 0.8);
            }

            QPushButton:pressed {
                background-color: rgba(255, 255, 255, 0.5);
            }
        """)
        top_save_nav.addWidget(self.btn_back)
        top_save_nav.addSpacing(10)

        title_save_row = QtWidgets.QLabel("💾 存档列表")
        title_save_row.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        title_save_row.setSizePolicy(
            QtWidgets.QSizePolicy.Policy.Maximum,
            QtWidgets.QSizePolicy.Policy.Fixed
        )
        title_save_row.setFixedHeight(36)
        title_save_row.setStyleSheet("""
             QLabel {
                 background: rgba(255, 255, 255, 0.8);
                 border-radius: 12px;
                 padding: 6px 16px;
                 font-size: 15px;
                 font-weight: 600;
                 color: #374151;
                 border: 1px solid rgba(0, 0, 0, 0.06);
             }
         """)
        top_save_nav.addWidget(title_save_row)
        top_save_nav.addStretch()
        saves_layout.addLayout(top_save_nav)

        self.saves_scroll = SmoothScrollArea()
        self.saves_container = QtWidgets.QWidget()
        self.saves_list_layout = QtWidgets.QVBoxLayout(self.saves_container)
        self.saves_list_layout.addStretch()
        self.saves_scroll.setWidget(self.saves_container)
        saves_layout.addWidget(self.saves_scroll)

        self.btn_open_saves_folder = QtWidgets.QPushButton("📁 打开存档文件夹")
        self.btn_open_saves_folder.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)
        self.btn_open_saves_folder.setFixedHeight(40)
        self.btn_open_saves_folder.setStyleSheet(
            "QPushButton { background: #2B7BE4; color: white; border-radius: 8px; font-weight: bold; font-size:14px; }")
        saves_layout.addWidget(self.btn_open_saves_folder)
        self.content_area.addWidget(self.saves_page)

        # 4. Save Detail
        self.save_detail_page = SaveDetailPage()
        self.content_area.addWidget(self.save_detail_page)

        # 5. Mod Manager
        self.mod_manager_page = ModManagerPage()
        self.content_area.addWidget(self.mod_manager_page)

        # 6. Overview Page
        self.overview_page = VersionOverviewPage()
        self.content_area.addWidget(self.overview_page)

        self.btn_save_info.clicked.connect(self.open_saves_requested.emit)
        self.btn_back.clicked.connect(self.show_settings)
        self.btn_open_mod_viewer.clicked.connect(self.open_mod_viewer_requested.emit)
        self.btn_overview.clicked.connect(self.open_overview_requested.emit)
        self.mod_manager_page.back_requested.connect(self.show_settings)
        self.overview_page.back_requested.connect(self.show_settings)
        self.overview_page.version_updated.connect(self.version_updated.emit)

        self.btn_add_api.clicked.connect(self.show_add_api_dialog_requested.emit)
        self.btn_add_game_root.clicked.connect(self.show_add_game_root_requested.emit)

    # =========================
    # 4) 图片显示 / 隐藏
    # =========================
    def show_mod_magic_image(self, icon_path: Optional[str] = None, size: int = 72):
        """
        显示 Mod 管理下方居中的图片。
        """
        if icon_path is not None:
            self.mod_magic_icon_path = icon_path
        apply_icon_to_label(self.mod_magic_label, self.mod_magic_icon_path, size)
        self.mod_magic_row.setVisible(True)

    def hide_mod_magic_image(self):
        """
        隐藏 Mod 管理下方的图片。
        """
        self.mod_magic_row.setVisible(False)

    # =========================
    # 5) 图片点击 -> 弹窗
    # =========================
    def _on_mod_magic_clicked(self):
        dlg = ModActionDialog(
            self,
            text="再召唤一次祝尼魔？"
        )
        dlg.possible_clicked.connect(self._handle_possible_clicked)
        dlg.other_clicked.connect(self._handle_other_clicked)
        dlg.exec()

    def _handle_possible_clicked(self):
        # 这里写“可能”对应的逻辑
        self.mod_magic_possible_requested.emit()

    def _handle_other_clicked(self, text: str):
        # 这里写其余按钮共用的逻辑
        self.mod_magic_other_requested.emit(text)

    def _style_groupbox(self, grp: QtWidgets.QGroupBox):
        grp.setStyleSheet("""
            QGroupBox { background-color: rgba(255, 255, 255, 0.75); border-radius: 12px; border: 1px solid #D1D5DB; margin-top: 0px; padding-top: 24px; font-size: 16px; font-weight: 700; color: #374151; }
            QGroupBox::title { subcontrol-origin: padding; subcontrol-position: top left; padding: 6px 12px; font-size: 15px; font-weight: 600; color: #1F2937; background-color: transparent; }
        """)

    def _style_settings_btn(self, btn: QtWidgets.QPushButton):
        btn.setFixedHeight(40)
        btn.setStyleSheet(
            "QPushButton { background: #FFFFFF; border: 1px solid rgba(0,0,0,0.1); border-radius: 6px; } QPushButton:hover { background: #F9FAFB; }")

    def _on_bg_combo_activated(self, idx: int):
        text = self.combo_bg.itemText(idx)
        if text == "📁 自定义背景...":
            path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "选择背景", "", "Images (*.png *.jpg *.jpeg *.gif)")
            if path:
                self.combo_bg.push_to_top(path, is_history=True)
                self.bg_changed.emit(path)
        elif text == "🎨 打开预设图库...":
            dlg = PresetGalleryDialog("选择背景预设", PRESETS, self)
            if dlg.exec() == QtWidgets.QDialog.DialogCode.Accepted:
                preset = dlg.selected_preset
                self.bg_changed.emit(preset)
        else:
            self.combo_bg.push_to_top(text, is_history=True)
            self.bg_changed.emit(text)

    def update_version_context(self, version: Optional[GameVersion]):
        self.current_version = version
        self.current_ver_preview.update_version(version)
        if version:
            self.btn_open_current_folder.setEnabled(True)
            self.btn_overview.setEnabled(True)
            if not version.is_modpack:
                self.btn_open_mod_viewer.setEnabled(False)
                self.btn_open_mod_viewer.setStyleSheet(
                    "QPushButton { background: #E5E7EB; color: #9CA3AF; border-radius: 6px; }")
                self.btn_open_mod_viewer.setText("🧩 Mod 管理 (仅整合包可用)")
            else:
                self.btn_open_mod_viewer.setEnabled(True)
                self.btn_open_mod_viewer.setStyleSheet(
                    "QPushButton { background: #F0F6FF; border: 1px solid #2B7BE4; color: #2B7BE4; border-radius: 6px; }")
                self.btn_open_mod_viewer.setText("🧩 Mod 管理")
        else:
            for b in (self.btn_open_current_folder, self.btn_open_mod_viewer, self.btn_overview): b.setEnabled(False)

    def show_empty(self):
        self.content_area.setCurrentIndex(0)

    def show_versions(self):
        self.content_area.setCurrentWidget(self.versions_page)

    def show_settings(self):
        self.content_area.setCurrentWidget(self.settings_page)

    def show_saves(self):
        self.content_area.setCurrentWidget(self.saves_page)

    def show_save_detail(self, save_name: str, config: LauncherConfig, versions: List[GameVersion]):
        meta = config.saves.get(save_name, SaveMetadata())
        version_label = resolve_version_display_name(meta.version_id, versions)
        self.save_detail_page.load_save(
            save_name,
            meta.icon_path,
            config.icon_history,
            meta.version_id,
            meta.note,
            version_label,
        )
        self.content_area.setCurrentWidget(self.save_detail_page)

    def show_mod_manager(self, version: GameVersion, global_notes: Dict[str, str], api_key: str = ""):
        self.mod_manager_page.nexus_api_key = api_key
        self.mod_manager_page.load_version(version, global_notes)
        self.content_area.setCurrentWidget(self.mod_manager_page)

    def show_overview(self, version: GameVersion):
        self.overview_page.load_version(version)
        self.content_area.setCurrentWidget(self.overview_page)

    def add_versions_list_row(self, widget: QtWidgets.QWidget):
        self.versions_list_layout.insertWidget(self.versions_list_layout.count() - 1, widget)

    def clear_saves_list(self):
        while self.saves_list_layout.count() > 1:
            i = self.saves_list_layout.takeAt(0)
            if i.widget(): i.widget().deleteLater()

    def add_save_row(self, widget: QtWidgets.QWidget):
        self.saves_list_layout.insertWidget(self.saves_list_layout.count() - 1, widget)






















































# =========================================================
# Data
# =========================================================

try:
    import psutil
except ImportError:
    print("no psutil")
    psutil = None


@dataclass(slots=True)
class FramePacket:
    ts_ms: int
    image: QtGui.QImage
    rgb_index: int = -1
    use_alpha: bool = False


class FrameInbox:
    """
    线程安全帧邮箱：
    worker 线程 append，UI 线程 drain。
    不再只保留最新帧，否则预生成完成后 show() 会丢掉前面的所有内容。
    """

    __slots__ = ("_lock", "_items")

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._items: Deque[FramePacket] = deque()

    def put(self, item: FramePacket) -> None:
        with self._lock:
            self._items.append(item)

    def drain_all(self) -> list[FramePacket]:
        with self._lock:
            if not self._items:
                return []
            items = list(self._items)
            self._items.clear()
            return items

    def is_empty(self) -> bool:
        with self._lock:
            return not self._items


class PlaybackState:
    """
    共享播放状态。
    worker 只依赖 playhead_ms，不依赖播放帧率做节拍控制。
    """

    __slots__ = ("_lock", "_started", "_playhead_ms")

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._started = False
        self._playhead_ms = 0

    def mark_started(self, playhead_ms: int) -> None:
        with self._lock:
            self._started = True
            self._playhead_ms = int(playhead_ms)

    def update_playhead_ms(self, playhead_ms: int) -> None:
        with self._lock:
            self._playhead_ms = int(playhead_ms)

    def snapshot(self) -> tuple[bool, int]:
        with self._lock:
            return self._started, self._playhead_ms


# =========================================================
# Generation controller
# =========================================================

class AdaptiveGenerationController:
    """
    生成侧节拍控制器。

    规则：
    - 未开始播放：固定 max_fps，绝不提前降速
    - 已开始播放：
      - 如果当前生成进度与播放进度“相差很远”，继续靠近 max_fps
      - 如果当前生成进度“接近播放进度”，跳帧更大，生成变慢
      - 不参考播放 fps 作为主驱动，避免播放端一抖动，生成端直接塌成 1fps
    """

    __slots__ = (
        "max_fps",
        "min_interval_ms",
        "slow_interval_ms",
        "near_window_ms",
        "ema_cost_ms",
        "_cooldown",
    )

    def __init__(
        self,
        max_fps: float = 60.0,
        near_window_ms: int = 2000,
        slow_skip_factor: float = 4.0,
    ) -> None:
        self.max_fps = float(max_fps)
        self.min_interval_ms = max(1, int(round(1000.0 / self.max_fps)))
        self.slow_interval_ms = max(self.min_interval_ms, int(round(self.min_interval_ms * slow_skip_factor)))
        self.near_window_ms = max(1, int(near_window_ms))
        self.ema_cost_ms = 0.0
        self._cooldown = 0

    @staticmethod
    def _lerp(a: float, b: float, t: float) -> float:
        t = max(0.0, min(1.0, t))
        return a + (b - a) * t

    def update(
        self,
        compose_cost_ms: float,
        playback_started: bool,
        lead_ms: int,
    ) -> int:
        """
        返回下一次允许输出的时间间隔（ms）。

        lead_ms = 当前候选帧时间戳 - 当前播放头时间戳
        - lead_ms <= 0 : 生成落后或齐平，直接 max_fps
        - lead_ms >= near_window_ms : 生成离播放足够远，也直接 max_fps
        - 0 ~ near_window_ms : 越接近播放头，越慢，跳帧越大
        """
        alpha = 0.18
        if self.ema_cost_ms <= 0:
            self.ema_cost_ms = float(compose_cost_ms)
        else:
            self.ema_cost_ms = self.ema_cost_ms * (1.0 - alpha) + float(compose_cost_ms) * alpha

        if not playback_started:
            return self.min_interval_ms

        if lead_ms <= 0 or lead_ms >= self.near_window_ms:
            interval_ms = self.min_interval_ms
        else:
            # lead 越接近 0，interval 越接近 slow_interval_ms
            t = lead_ms / float(self.near_window_ms)
            interval_ms = int(round(self._lerp(self.slow_interval_ms, self.min_interval_ms, t)))

        # 合成成本过高时，只做轻微收紧，不允许塌到极低帧率
        if self._cooldown > 0:
            self._cooldown -= 1
        else:
            if self.ema_cost_ms > interval_ms * 0.90:
                interval_ms = int(round(interval_ms * 1.10))
                self._cooldown = 2

        return max(1, interval_ms)


# =========================================================
# Worker
# =========================================================

class _BufferedDualStreamCompositeWorker(QtCore.QObject):
    finished = QtCore.Signal()
    error = QtCore.Signal(str)

    def __init__(
        self,
        rgb_path: str,
        alpha_path: str,
        inbox: FrameInbox,
        playback_state: PlaybackState,
        stop_event: threading.Event,
        ui_started_event: threading.Event,
        sync_eps_ms: int = 20,
        max_fps: float = 60.0,
        alpha_head_frames: int = 600,
        alpha_tail_frames: int = 600,
    ) -> None:
        super().__init__()
        self._rgb_path = rgb_path
        self._alpha_path = alpha_path
        self._inbox = inbox
        self._playback_state = playback_state
        self._stop_event = stop_event
        self._ui_started_event = ui_started_event
        self._sync_eps_ms = int(sync_eps_ms)
        self._alpha_head_frames = max(0, int(alpha_head_frames))
        self._alpha_tail_frames = max(0, int(alpha_tail_frames))
        self.frame_count = 0
        self.rss_limit = 2 * 1024 * 1024 * 1024

        source_fps = self._probe_source_fps(self._rgb_path)
        if source_fps > 0:
            max_fps = min(float(max_fps), source_fps)
        self._source_fps = source_fps

        self._controller = AdaptiveGenerationController(
            max_fps=max_fps if max_fps > 0 else 60.0,
            near_window_ms=2000,
            slow_skip_factor=4.0,
        )

        self._total_frames = self._probe_total_frames_exact(self._rgb_path)
        self._alpha_start_index = max(0, self._total_frames - self._alpha_tail_frames)

        self._next_emit_ts_ms = -1
        self._last_mem_check_mono = 0.0

    @staticmethod
    def _probe_source_fps(path: str) -> float:
        try:
            with av.open(path) as container:
                stream = container.streams.video[0]
                rate = stream.average_rate or stream.guessed_rate
                if rate is not None:
                    return float(rate)
        except Exception:
            pass
        return 0.0

    @staticmethod
    def _probe_total_frames_exact(path: str) -> int:
        """
        尽量获取精确总帧数：
        1) 优先 metadata
        2) 失败时全量计数
        """
        try:
            with av.open(path) as container:
                stream = container.streams.video[0]
                if stream.frames and int(stream.frames) > 0:
                    return int(stream.frames)
        except Exception:
            pass

        count = 0
        try:
            with av.open(path) as container:
                for _ in container.decode(video=0):
                    count += 1
        except Exception:
            pass
        return count

    def _maybe_throttle_for_memory(self) -> None:
        """
        未开始显示前，如果进程 RSS > 2GiB 且系统内存占用 > 92%，
        每次最多检查一次；条件持续满足时，循环 sleep 1 秒。
        一旦 UI 已开始显示（_started=True 对应的事件已 set），立即放行。
        """
        if self._ui_started_event.is_set():
            return

        if psutil is None:
            return

        now = time.monotonic()
        if now - self._last_mem_check_mono < 1.0:
            return
        self._last_mem_check_mono = now
        print(f'_maybe_throttle_for_memory frame_count: {self.frame_count}')
          # 2GiB

        while not self._stop_event.is_set() and not self._ui_started_event.is_set():
            try:
                proc = psutil.Process(os.getpid())
                rss = proc.memory_info().rss
                overall_percent = psutil.virtual_memory().percent
            except Exception:
                return

            if not (rss > self.rss_limit and overall_percent > 92.0):
                return

            time.sleep(1.0)

    @QtCore.Slot()
    def run(self) -> None:
        try:
            with (
                av.open(self._rgb_path) as rgb_container,
                av.open(self._alpha_path) as alpha_container,
            ):
                rgb_stream = rgb_container.streams.video[0]
                alpha_stream = alpha_container.streams.video[0]

                for s in (rgb_stream, alpha_stream):
                    try:
                        s.thread_type = "AUTO"
                    except Exception:
                        pass

                rgb_iter = rgb_container.decode(video=0)
                alpha_iter = alpha_container.decode(video=0)

                rgb_frame = next(rgb_iter, None)
                alpha_frame = next(alpha_iter, None)

                if rgb_frame is None or alpha_frame is None:
                    return

                rgb_index = 0
                alpha_index = 0

                while not self._stop_event.is_set():
                    if rgb_frame is None or alpha_frame is None:
                        break

                    rgb_t = self._frame_time_ms(rgb_frame, rgb_stream)
                    alpha_t = self._frame_time_ms(alpha_frame, alpha_stream)
                    delta = rgb_t - alpha_t

                    if abs(delta) > self._sync_eps_ms:
                        if delta < 0:
                            rgb_frame = next(rgb_iter, None)
                            rgb_index += 1
                        else:
                            alpha_frame = next(alpha_iter, None)
                            alpha_index += 1
                        continue

                    ts_ms = max(rgb_t, alpha_t)

                    playback_started, playhead_ms = self._playback_state.snapshot()
                    lead_ms = ts_ms - playhead_ms

                    # 未开始播放：永远按 max_fps 连续生成，不跳帧
                    if not playback_started:
                        should_emit = True
                    else:
                        if self._next_emit_ts_ms < 0:
                            self._next_emit_ts_ms = ts_ms
                        should_emit = ts_ms >= self._next_emit_ts_ms

                    if not should_emit:
                        # 当前帧不输出，继续推进解码
                        rgb_frame = next(rgb_iter, None)
                        alpha_frame = next(alpha_iter, None)
                        rgb_index += 1
                        alpha_index += 1
                        continue

                    t0 = QtCore.QElapsedTimer()
                    t0.start()

                    self.frame_count += 1
                    # print(self.frame_count)

                    use_alpha = self._should_use_alpha(rgb_index)
                    packet = self._compose_to_packet(
                        rgb_frame=rgb_frame,
                        alpha_frame=alpha_frame if use_alpha else None,
                        ts_ms=ts_ms,
                        rgb_index=rgb_index,
                        use_alpha=use_alpha,
                    )
                    compose_cost_ms = t0.nsecsElapsed() / 1_000_000.0

                    self._inbox.put(packet)

                    target_interval_ms = self._controller.update(
                        compose_cost_ms=compose_cost_ms,
                        playback_started=playback_started,
                        lead_ms=lead_ms,
                    )

                    self._next_emit_ts_ms = ts_ms + target_interval_ms

                    rgb_frame = next(rgb_iter, None)
                    alpha_frame = next(alpha_iter, None)
                    rgb_index += 1
                    alpha_index += 1

        except Exception:
            msg = traceback.format_exc()
            print("[worker] fatal exception:")
            print(msg)
            self.error.emit(msg)
        finally:
            self.finished.emit()

    def stop(self) -> None:
        self._stop_event.set()

    def _should_use_alpha(self, rgb_index: int) -> bool:
        if rgb_index < 0:
            return False
        if self._total_frames <= 0:
            return rgb_index < self._alpha_head_frames
        return rgb_index < self._alpha_head_frames or rgb_index >= self._alpha_start_index

    @staticmethod
    def _frame_time_ms(frame: av.VideoFrame, stream: av.video.stream.VideoStream) -> int:
        if frame.pts is not None:
            tb = frame.time_base or stream.time_base
            if tb is not None:
                return int(round(float(frame.pts * tb) * 1000.0))

        if frame.time is not None:
            return int(round(float(frame.time) * 1000.0))

        return 0

    def _compose_to_packet(
        self,
        rgb_frame: av.VideoFrame,
        alpha_frame: av.VideoFrame | None,
        ts_ms: int,
        rgb_index: int,
        use_alpha: bool,
    ) -> FramePacket:
        self._maybe_throttle_for_memory()

        rgb = rgb_frame.to_ndarray(format="rgb24")
        h, w = rgb.shape[:2]

        if not use_alpha or alpha_frame is None:
            image = QtGui.QImage(
                rgb.data,
                w,
                h,
                rgb.strides[0],
                QtGui.QImage.Format.Format_RGB888,
            ).copy()
            return FramePacket(ts_ms=ts_ms, image=image, rgb_index=rgb_index, use_alpha=False)

        alpha = alpha_frame.to_ndarray(format="gray")
        if alpha.ndim == 3:
            alpha = alpha[:, :, 0]

        if alpha.shape[0] != h or alpha.shape[1] != w:
            alpha_frame = alpha_frame.reformat(width=w, height=h, format="gray")
            alpha = alpha_frame.to_ndarray(format="gray")
            if alpha.ndim == 3:
                alpha = alpha[:, :, 0]

        rgba = np.empty((h, w, 4), dtype=np.uint8)
        rgba[:, :, 0:3] = rgb
        rgba[:, :, 3] = alpha

        image = QtGui.QImage(
            rgba.data,
            w,
            h,
            rgba.strides[0],
            QtGui.QImage.Format.Format_RGBA8888,
        ).copy()

        return FramePacket(ts_ms=ts_ms, image=image, rgb_index=rgb_index, use_alpha=True)


# =========================================================
# Window
# =========================================================

class FullscreenAlphaCompositeVideoWindow(QtWidgets.QWidget):
    def __init__(
        self,
        rgb_video_path: str | Path,
        alpha_video_path: str | Path,
        buffer_frames: int = 1,
        start_buffer_frames: int = 1,
        late_drop_ms: int = 80,
        lead_show_ms: int = 15,
        render_tick_ms: int = 8,
        hard_fallback_ms: int = 120,
        alpha_head_frames: int = 600,
        alpha_tail_frames: int = 600,
        min_fps: float = 30.0,
        max_fps: float = 60.0,
        initial_fps: float = 60.0,
    ) -> None:
        super().__init__()

        self._allow_close = False
        self._started = False
        self._worker_started = False
        self._decoder_done = False
        self._playback_started = False

        self._rgb_video_path = str(rgb_video_path)
        self._alpha_video_path = str(alpha_video_path)

        self._inbox = FrameInbox()
        self._local_buffer: Deque[FramePacket] = deque()
        self._stop_event = threading.Event()
        self._playback_state = PlaybackState()
        self._ui_started_event = threading.Event()

        self._start_buffer_frames = max(1, int(start_buffer_frames))
        self._late_drop_ms = int(late_drop_ms)
        self._lead_show_ms = int(lead_show_ms)
        self._render_tick_ms = int(render_tick_ms)
        self._hard_fallback_ms = int(hard_fallback_ms)

        self._alpha_head_frames = max(0, int(alpha_head_frames))
        self._alpha_tail_frames = max(0, int(alpha_tail_frames))
        self._min_fps = float(min_fps)
        self._max_fps = float(max_fps)
        self._initial_fps = float(initial_fps)

        self._current_packet: FramePacket | None = None
        self._current_image = QtGui.QImage()

        self._playback_clock = QtCore.QElapsedTimer()
        self._playback_clock_started = False
        self._playback_origin_ms = 0

        self._last_present_elapsed = 0
        self._missed_render_ticks = 0
        self._last_present_packet_ts_ms = -1
        self._playback_fps_ema = 0.0
        self._eof_grace_started_at_ms: int | None = None

        self.setWindowTitle("Happy Birthday")
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            | QtCore.Qt.WindowType.WindowStaysOnTopHint
            | QtCore.Qt.WindowType.Tool
        )

        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAutoFillBackground(False)
        self.setStyleSheet("background: transparent;")
        self.setFocusPolicy(QtCore.Qt.FocusPolicy.StrongFocus)

        # ---------------------------
        # Audio
        # ---------------------------
        self._audio_output = QtMultimedia.QAudioOutput(self)
        self._audio_output.setVolume(1.0)

        self._audio_player = QtMultimedia.QMediaPlayer(self)
        self._audio_player.setAudioOutput(self._audio_output)
        self._audio_player.setSource(QtCore.QUrl.fromLocalFile(self._rgb_video_path))

        # ---------------------------
        # Render timer
        # ---------------------------
        self._render_timer = QtCore.QTimer(self)
        self._render_timer.setTimerType(QtCore.Qt.TimerType.PreciseTimer)
        self._render_timer.timeout.connect(self._sync_render_tick)

        self.frame_index = 0

        if not self._worker_started:
            self._start_worker()

    def showEvent(self, event: QtGui.QShowEvent) -> None:
        super().showEvent(event)

        if self._started:
            return

        self._started = True
        self._ui_started_event.set()
        self.update()
        QtCore.QTimer.singleShot(0, self._post_show_setup)

    def _post_show_setup(self) -> None:
        if not self.isVisible():
            return

        try:
            self.showFullScreen()
        except Exception:
            pass

        try:
            self.raise_()
        except Exception:
            pass

        try:
            self.activateWindow()
        except Exception:
            pass

        try:
            self.setFocus()
        except Exception:
            pass

        if not self._render_timer.isActive():
            self._render_timer.start(self._render_tick_ms)

        if not self._worker_started:
            self._start_worker()

        self._sync_render_tick()

    def paintEvent(self, event: QtGui.QPaintEvent) -> None:
        painter = QtGui.QPainter(self)

        if self._current_image.isNull():
            return

        painter.fillRect(self.rect(), QtCore.Qt.GlobalColor.transparent)
        painter.setRenderHint(QtGui.QPainter.RenderHint.SmoothPixmapTransform, False)

        target_rect = self._fit_rect(self._current_image.size(), self.rect())
        if not target_rect.isValid():
            return

        painter.drawImage(target_rect, self._current_image)

    def closeEvent(self, event: QtGui.QCloseEvent) -> None:
        if self._allow_close:
            self._stop_all()
            event.accept()
            return
        event.ignore()

    # =========================================================
    # Playback
    # =========================================================

    def _start_worker(self) -> None:
        if self._worker_started:
            return

        self._worker_started = True
        self._thread = QtCore.QThread(self)
        self._worker = _BufferedDualStreamCompositeWorker(
            self._rgb_video_path,
            self._alpha_video_path,
            self._inbox,
            self._playback_state,
            self._stop_event,
            self._ui_started_event,
            sync_eps_ms=20,
            max_fps=self._max_fps,
            alpha_head_frames=self._alpha_head_frames,
            alpha_tail_frames=self._alpha_tail_frames,
        )

        self._worker.moveToThread(self._thread)
        self._thread.started.connect(self._worker.run)

        self._worker.finished.connect(self._on_worker_finished)
        self._worker.error.connect(self._on_worker_error)

        self._worker.finished.connect(self._thread.quit)
        self._worker.finished.connect(self._worker.deleteLater)
        self._thread.finished.connect(self._thread.deleteLater)

        self._thread.start()

    @QtCore.Slot()
    def _maybe_start_playback(self) -> None:
        if self._playback_started or not self.isVisible():
            return

        self._drain_incoming_queue()

        if not self._local_buffer:
            return

        if not (self._decoder_done or len(self._local_buffer) >= self._start_buffer_frames):
            return

        self._playback_started = True

        first_packet = self._local_buffer[0]
        self._playback_origin_ms = first_packet.ts_ms
        self._playback_state.mark_started(self._playback_origin_ms)

        self._playback_clock.start()
        self._playback_clock_started = True
        self._last_present_elapsed = 0
        self._missed_render_ticks = 0
        self._playback_fps_ema = 0.0
        self._eof_grace_started_at_ms = None

        self._present_due_frame()

        try:
            self._audio_player.play()
        except Exception:
            pass

    @QtCore.Slot()
    def _sync_render_tick(self) -> None:
        if self._stop_event.is_set():
            return

        self._drain_incoming_queue()

        if not self._playback_started:
            self._maybe_start_playback()
            if self._current_image.isNull():
                self.update()
            return

        self._present_due_frame()

        if self._decoder_done and not self._local_buffer and self._inbox.is_empty():
            if self._audio_is_done():
                if self._eof_grace_started_at_ms is None:
                    self._eof_grace_started_at_ms = int(self._playback_clock.elapsed())
                elif int(self._playback_clock.elapsed()) - self._eof_grace_started_at_ms >= self._hard_fallback_ms:
                    self._allow_close = True
                    self.close()
            else:
                self._eof_grace_started_at_ms = None
        else:
            self._eof_grace_started_at_ms = None

    def _present_due_frame(self) -> None:
        playhead_ms = self._current_playhead_ms()
        self._playback_state.update_playhead_ms(playhead_ms)

        packet = self._select_packet(playhead_ms)
        if packet is not None:
            self._present_packet(packet)

    def _present_packet(self, packet: FramePacket) -> None:
        if packet is self._current_packet:
            return

        self.frame_index += 1
        if self.frame_index == 1:
            QtCore.QTimer.singleShot(9000, lambda: self.set_video_click_through(False))
            QtCore.QTimer.singleShot(40000, lambda: self.set_video_click_through(True))
            QtCore.QTimer.singleShot(44000, self.triggered)

        now_elapsed = self._playback_clock.elapsed()
        if self._last_present_elapsed > 0:
            delta = now_elapsed - self._last_present_elapsed
            if delta > 0:
                fps = 1000.0 / float(delta)
                if self._playback_fps_ema <= 0:
                    self._playback_fps_ema = fps
                else:
                    self._playback_fps_ema = self._playback_fps_ema * 0.82 + fps * 0.18

        self._last_present_elapsed = now_elapsed
        self._last_present_packet_ts_ms = max(self._last_present_packet_ts_ms, packet.ts_ms)

        self._current_packet = packet
        self._current_image = packet.image
        self.update()

    def _select_packet(self, playhead_ms: int) -> FramePacket | None:
        while self._local_buffer and self._local_buffer[0].ts_ms < playhead_ms - self._late_drop_ms:
            self._local_buffer.popleft()

        latest_eligible: FramePacket | None = None
        while self._local_buffer and self._local_buffer[0].ts_ms <= playhead_ms + self._lead_show_ms:
            latest_eligible = self._local_buffer.popleft()

        if latest_eligible is not None:
            return latest_eligible

        if self._local_buffer:
            return self._local_buffer[0]

        mailbox_item = self._drain_one_from_inbox()
        if mailbox_item is not None:
            return mailbox_item

        return self._current_packet

    def _current_playhead_ms(self) -> int:
        """
        播放头以墙钟推进，起点为第一帧时间戳。
        不依赖 QMediaPlayer.position() 驱动画面节奏，避免后端更新太粗。
        """
        if not self._playback_clock_started or not self._playback_clock.isValid():
            return 0
        return int(self._playback_origin_ms + self._playback_clock.elapsed())

    def _drain_incoming_queue(self) -> None:
        items = self._inbox.drain_all()
        if items:
            self._local_buffer.extend(items)

    def _drain_one_from_inbox(self) -> FramePacket | None:
        items = self._inbox.drain_all()
        if not items:
            return None
        self._local_buffer.extend(items)
        return self._local_buffer.popleft() if self._local_buffer else None

    def _audio_is_done(self) -> bool:
        try:
            state = self._audio_player.playbackState()
            if state == QtMultimedia.QMediaPlayer.PlaybackState.StoppedState:
                return True

            status = self._audio_player.mediaStatus()
            if status in (
                QtMultimedia.QMediaPlayer.MediaStatus.EndOfMedia,
                QtMultimedia.QMediaPlayer.MediaStatus.InvalidMedia,
            ):
                return True
        except Exception:
            pass
        return False

    # =========================================================
    # Utils
    # =========================================================

    @staticmethod
    def _fit_rect(src_size: QtCore.QSize, bounds: QtCore.QRect) -> QtCore.QRect:
        if src_size.isEmpty() or bounds.isEmpty():
            return QtCore.QRect()

        scaled = src_size.scaled(
            bounds.size(),
            QtCore.Qt.AspectRatioMode.KeepAspectRatio,
        )

        rect = QtCore.QRect(QtCore.QPoint(0, 0), scaled)
        rect.moveCenter(bounds.center())
        return rect

    # =========================================================
    # Slots
    # =========================================================

    @QtCore.Slot()
    def _on_worker_finished(self) -> None:
        self._decoder_done = True
        self._drain_incoming_queue()

        if self.isVisible() and not self._playback_started and self._local_buffer:
            self._maybe_start_playback()

        print("_on_worker_finished finish")

    @QtCore.Slot(str)
    def _on_worker_error(self, message: str) -> None:
        print("Video worker error:")
        print(message)
        self._allow_close = True
        self.close()

    # =========================================================
    # Public
    # =========================================================

    def triggered(self) -> None:
        """
        保留你的外部钩子逻辑；做了容错，避免未定义全局变量直接炸掉。
        """
        try:
            if "TRIGGERED_FILE_PATH" in globals():
                TRIGGERED_FILE_PATH.touch(exist_ok=True)  # type: ignore[name-defined]
            if "b_event" in globals():
                b_event.is_triggered = True  # type: ignore[name-defined]
        except Exception:
            pass

    def set_video_click_through(self, enabled: bool) -> None:
        print(f"set_video_click_through {enabled}")
        if sys.platform.startswith("win"):
            import ctypes

            hwnd = int(self.winId())
            GWL_EXSTYLE = -20
            WS_EX_TRANSPARENT = 0x00000020
            WS_EX_LAYERED = 0x00080000

            user32 = ctypes.windll.user32
            style = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)

            if enabled:
                style |= WS_EX_LAYERED
                style |= WS_EX_TRANSPARENT
            else:
                style &= ~WS_EX_TRANSPARENT

            user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)
        else:
            self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents, enabled)

    # =========================================================
    # Stop
    # =========================================================

    def _stop_all(self) -> None:
        try:
            self._stop_event.set()
        except Exception:
            pass

        try:
            self._audio_player.stop()
        except Exception:
            pass

        try:
            if self._render_timer.isActive():
                self._render_timer.stop()
        except Exception:
            pass

        try:
            if hasattr(self, "_thread") and self._thread.isRunning():
                self._thread.quit()
                self._thread.wait(1500)
        except Exception:
            pass

    def close(self) -> bool:
        self._stop_all()
        return super().close()


def b_video_create(is_refresh=False):
    global mov
    if not isinstance(mov, FullscreenAlphaCompositeVideoWindow) or (is_refresh and mov._allow_close):
        mov = FullscreenAlphaCompositeVideoWindow(
            B_EVENT_PATH / "main_720p.mp4",
            B_EVENT_PATH / "alpha_720p.mp4",
            buffer_frames=2890,  # 从 8 -> 12，稍微加点缓冲
            start_buffer_frames=0,  # 立刻开始播放（只需 1 帧）
            late_drop_ms=80,
            lead_show_ms=15,
            render_tick_ms=13,
            hard_fallback_ms=120,
        )
    return mov
# 你是专业的python工程师 pyside6，请你仔细阅读下面这个视频播放代码，修改代码确保其稳定性
# 1. 实例化的时候尽可能的开始加载缓存
# 2. 调用show()的时候立刻出现
# 3. 一定要完全避免视频播放时卡住的情况，现在如果加载帧数不多，以及低端电脑中仍有完全卡住的风险，一定要跳帧追赶进度
# 修改后输出全部代码
class FloatingGifWidget(QtWidgets.QWidget):
    gif_clicked = QtCore.Signal()

    def __init__(
            self,
            gif_path: str | Path,
            parent: Optional[QtWidgets.QWidget] = None,
            scale: float = 1.0,
            anchor: tuple[float, float] = (0.75, 0.90),
    ):
        super().__init__(parent)

        self.mov = None
        self._gif_path = str(gif_path)
        self._scale = float(scale)
        self._anchor_x, self._anchor_y = anchor

        self._angle = 0.0
        self._animation: Optional[QtCore.QAbstractAnimation] = None
        self._original_parent = parent

        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents, False)
        self.setCursor(QtCore.Qt.CursorShape.PointingHandCursor)

        self._movie = QtGui.QMovie(self._gif_path)
        self._movie.setCacheMode(QtGui.QMovie.CacheMode.CacheAll)
        self._movie.frameChanged.connect(self.update)

        self._base_size = self._resolve_gif_size()
        self._content_size = QtCore.QSize()

        self._apply_scale()

    def _resolve_gif_size(self) -> QtCore.QSize:
        self._movie.start()
        self._movie.jumpToFrame(0)

        size = self._movie.currentPixmap().size()
        if size.isEmpty():
            size = self._movie.frameRect().size()

        self._movie.stop()

        if size.isEmpty():
            size = QtCore.QSize(64, 64)

        return size

    def _apply_scale(self) -> None:
        w = max(1, int(self._base_size.width() * self._scale))
        h = max(1, int(self._base_size.height() * self._scale))

        safe_side = int((w * w + h * h) ** 0.5) + 4
        self._content_size = QtCore.QSize(w, h)

        self._movie.setScaledSize(self._content_size)
        self.setFixedSize(safe_side, safe_side)

        self._movie.start()
        self.update_anchor_position()

    def set_scale(self, scale: float) -> None:
        self._scale = max(0.1, float(scale))
        self._apply_scale()

    def set_anchor(self, x: float, y: float) -> None:
        self._anchor_x = max(0.0, min(1.0, float(x)))
        self._anchor_y = max(0.0, min(1.0, float(y)))
        self.update_anchor_position()

    def update_anchor_position(self) -> None:
        parent = self.parentWidget()
        if not parent:
            return

        px = int((parent.width() - self.width()) * self._anchor_x)
        py = int((parent.height() - self.height()) * self._anchor_y)
        self.move(max(0, px), max(0, py))

    @QtCore.Property(float)
    def angle(self) -> float:
        return self._angle

    @angle.setter
    def angle(self, value: float) -> None:
        self._angle = float(value)
        self.update()

    def paintEvent(self, event: QtGui.QPaintEvent) -> None:
        pm = self._movie.currentPixmap()
        if pm.isNull():
            return

        painter = QtGui.QPainter(self)
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing, True)
        painter.setRenderHint(QtGui.QPainter.RenderHint.SmoothPixmapTransform, True)

        painter.translate(self.rect().center())
        painter.rotate(self._angle)

        target = QtCore.QRect(
            -self._content_size.width() // 2,
            -self._content_size.height() // 2,
            self._content_size.width(),
            self._content_size.height(),
        )
        painter.drawPixmap(target, pm)

    def mousePressEvent(self, event: QtGui.QMouseEvent) -> None:
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self.gif_clicked.emit()
            self.play_sequence()
        super().mousePressEvent(event)

    def _to_global_floating(self) -> None:
        global_pos = self.mapToGlobal(QtCore.QPoint(0, 0))

        self.setParent(None)
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            | QtCore.Qt.WindowType.Tool
            | QtCore.Qt.WindowType.WindowStaysOnTopHint
        )
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground, True)

        self.show()
        self.move(global_pos)

    def _restore_to_parent(self) -> None:
        parent = self._original_parent
        if parent:
            self.setParent(parent)
            self.setWindowFlags(QtCore.Qt.WindowType.Widget)
            self.show()
            self.update_anchor_position()

    def play_sequence(self) -> None:
        if self._animation and self._animation.state() == QtCore.QAbstractAnimation.State.Running:
            return

        self.show()
        self.raise_()

        start_pos = self.pos()

        # 更像真实跳跃：上升快、接近顶点减速、下落加速
        peak_pos = start_pos + QtCore.QPoint(0, -max(28, int(self.height() * 0.32)))

        rise = QtCore.QPropertyAnimation(self, b"pos", self)
        rise.setDuration(550)
        rise.setStartValue(start_pos)
        rise.setEndValue(peak_pos)
        rise.setEasingCurve(QtCore.QEasingCurve.Type.OutCubic)

        fall = QtCore.QPropertyAnimation(self, b"pos", self)
        fall.setDuration(950)
        fall.setStartValue(peak_pos)
        fall.setEndValue(start_pos)
        fall.setEasingCurve(QtCore.QEasingCurve.Type.InQuad)

        pause = QtCore.QPauseAnimation(1000, self)

        seq = QtCore.QSequentialAnimationGroup(self)
        seq.addAnimation(rise)
        seq.addAnimation(fall)
        seq.addAnimation(pause)
        seq.finished.connect(self._start_global_fly)

        self._animation = seq
        seq.start(QtCore.QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)
        # self.mov = FullscreenAlphaCompositeVideoWindow(
        #     r"E:\Pathstar\Video\AE\Pixel_Birthday_26-04-25\main_720p.mp4",
        #     r"E:\Pathstar\Video\AE\Pixel_Birthday_26-04-25\alpha_720p.mp4",
        #     buffer_frames=300,  # 从 8 -> 12，稍微加点缓冲
        #     start_buffer_frames=60,  # 立刻开始播放（只需 1 帧）
        #     late_drop_ms=80,
        #     lead_show_ms=15,
        #     render_tick_ms=16,
        #     hard_fallback_ms=120,
        # )

        def mov_player():
            print("mov_player")
            if isinstance(mov, FullscreenAlphaCompositeVideoWindow):
                mov.show()
                mov.set_video_click_through(True)

        junimo_sound.play()
        QtCore.QTimer.singleShot(7000, mov_player)

    def show_cake(self):
        pass



    def _start_global_fly(self) -> None:
        self._animation = None

        # 跳跃和停顿结束后，再切到全局坐标，避免瞬移
        self._to_global_floating()

        global_start = self.pos()

        screen = QtGui.QGuiApplication.screenAt(self.mapToGlobal(self.rect().center()))
        if screen is None:
            screen = QtGui.QGuiApplication.primaryScreen()

        screen_top = screen.geometry().top() if screen else 0
        end_pos = QtCore.QPoint(global_start.x(), screen_top - self.height() - 20)

        move = QtCore.QPropertyAnimation(self, b"pos", self)
        move.setDuration(4000)
        move.setStartValue(global_start)
        move.setEndValue(end_pos)
        move.setEasingCurve(QtCore.QEasingCurve.Type.Linear)

        rotate = QtCore.QPropertyAnimation(self, b"angle", self)
        rotate.setDuration(4000)
        rotate.setStartValue(self._angle)
        rotate.setEndValue(self._angle + 720.0)
        rotate.setEasingCurve(QtCore.QEasingCurve.Type.Linear)

        fly = QtCore.QParallelAnimationGroup(self)
        fly.addAnimation(move)
        fly.addAnimation(rotate)
        fly.finished.connect(self._on_sequence_finished)

        self._animation = fly
        fly.start(QtCore.QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)

    def _on_sequence_finished(self) -> None:
        self._animation = None
        self.hide()

    def set_gif_visible(self, visible: bool) -> None:
        if visible:
            self._restore_to_parent()
            self.show()
            self.raise_()
        else:
            if self._animation and self._animation.state() == QtCore.QAbstractAnimation.State.Running:
                self._animation.stop()
                self._animation = None
            self.hide()


# -------------------------
# Main Application
# -------------------------
class LauncherMainWindow(QtWidgets.QMainWindow):
    def __init__(self, game_root: Path, config_path: Path):
        super().__init__()
        self.game_root = game_root
        self.config_path = config_path
        self.config = load_config(self.config_path)

        # Migrate old saves config (version -> version_id mappings if possible)
        for _, meta in self.config.saves.items():
            if not meta.version_id and hasattr(meta, 'version'):
                # Simple fallback
                meta.version_id = getattr(meta, 'version', '')

        self.bg_movie: Optional[QtGui.QMovie] = None
        self._bg_original_pixmap: Optional[QtGui.QPixmap] = None
        self._bg_movie_original_size: QtCore.QSize = QtCore.QSize()
        self._scanned_versions: List[GameVersion] = []

        self._init_ui()
        self._load_state()
        self.refresh_versions()

    def _init_ui(self):
        self.setWindowTitle("Stardew Valley Launcher")
        self.setMinimumSize(850, 600)
        self.resize(900, 650)

        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        central_layout = QtWidgets.QVBoxLayout(central)
        central_layout.setContentsMargins(0, 0, 0, 0)

        self.bg_label = QtWidgets.QLabel(central)
        self.bg_label.setScaledContents(False)
        self.bg_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)

        overlay = QtWidgets.QWidget(central)
        overlay_layout = QtWidgets.QHBoxLayout(overlay)
        overlay_layout.setContentsMargins(0, 0, 0, 0)
        overlay_layout.setSpacing(0)

        # 动态创建 LeftPane, TipBubble 等...
        # （假设原依赖类均已合并进同一文件）
        self.left_pane = LeftPane(fixed_width=260, parent=overlay, main_window=self)
        self.right_pane = RightPane(parent=overlay)

        overlay_layout.addWidget(self.left_pane)
        overlay_layout.addWidget(self.right_pane, 1)

        self.overlay = overlay
        overlay.raise_()

        self.left_pane.version_selected.connect(self.on_launch_version)
        self.left_pane.open_settings.connect(self.right_pane.show_settings)
        self.left_pane.open_version_selector.connect(self.right_pane.show_versions)

        self.right_pane.bg_changed.connect(self.on_set_background_str)
        self.right_pane.bg_history_removed.connect(self._on_bg_history_removed)
        self.right_pane.overview_page.icon_history_removed.connect(self._on_icon_history_removed)
        self.right_pane.save_detail_page.icon_history_removed.connect(self._on_icon_history_removed)
        self.right_pane.mod_manager_page.mod_note_changed.connect(self._on_mod_note_changed)

        self.right_pane.version_updated.connect(self._on_version_meta_updated)

        self.right_pane.btn_open_current_folder.clicked.connect(self.on_open_current_folder)
        self.right_pane.open_saves_requested.connect(self.show_saves_list)
        self.right_pane.btn_open_saves_folder.clicked.connect(self.on_open_saves_folder)
        self.right_pane.open_mod_viewer_requested.connect(self.show_mod_viewer)
        self.right_pane.open_overview_requested.connect(self.show_overview)

        self.right_pane.save_detail_page.back_requested.connect(self.show_saves_list)
        self.right_pane.save_detail_page.backup_requested.connect(self.handle_save_backup)
        self.right_pane.save_detail_page.delete_requested.connect(self.handle_save_delete)
        self.right_pane.save_detail_page.icon_changed.connect(self._on_save_icon_changed)
        self.right_pane.save_detail_page.open_folder_requested.connect(self._on_save_open_folder)

        self.right_pane.show_add_api_dialog_requested.connect(self.show_add_api_dialog)
        self.right_pane.show_add_game_root_requested.connect(self.show_add_game_root)

        self.right_pane.mod_magic_possible_requested.connect(self.junimo_possible)
        self.right_pane.mod_magic_other_requested.connect(self.junimo_show)

        self.setStyleSheet("QMainWindow { background: #f3f4f6; } QLabel { font-family: 'Segoe UI', system-ui; }")

        # GIF：放在窗口相对坐标 (0.75, 0.9)，缩放 4 倍
        gif_path = B_EVENT_PATH / "junimo.gif"
        self.floating_gif = FloatingGifWidget(
            gif_path=gif_path,
            parent=self.overlay,
            scale=1.0,
            anchor=(0.9, 1),
        )
        self.floating_gif.set_gif_visible(b_event.is_today and not b_event.is_triggered)
        self.floating_gif.raise_()
        self.floating_gif.gif_clicked.connect(self.floating_gif_play_sequence)
        global mov

        def job():
            b_video_create()
            self.floating_gif.set_gif_visible(True)

        task_schd.add_job(
            job,
            trigger="date",
            run_date=b_event.datetime,
            # kwargs={"event_dt": event_dt, "delta": delta, "event_name": event_name},
            id=f"b_event_begin",
            misfire_grace_time=8
        )

        if b_event.is_2026:
            b_video_create()

    def floating_gif_play_sequence(self):
        QtCore.QTimer.singleShot(38000, lambda: self.right_pane.mod_magic_row.setVisible(True))

    def junimo_possible(self):
        self.left_pane.center_gif._play_clicked()
        self.left_pane.show_tip("祝尼魔跑咯~")

    def junimo_show(self, s: str):
        b_video_create(is_refresh=True)
        self.left_pane.center_gif._play_clicked()
        gif_path = B_EVENT_PATH / "junimo.gif"
        self.floating_gif = FloatingGifWidget(
            gif_path=gif_path,
            parent=self.overlay,
            scale=1.0,
            anchor=(0.9, 1),
        )
        self.floating_gif.set_gif_visible(True)
        self.floating_gif.raise_()

    def set_gif_visible(self, visible: bool) -> None:
        if hasattr(self, "floating_gif"):
            self.floating_gif.set_gif_visible(visible)

    def _on_bg_history_removed(self, text: str):
        if text in self.config.bg_history:
            self.config.bg_history.remove(text)
            save_config(self.config, self.config_path)

    def _on_icon_history_removed(self, text: str):
        if text in self.config.icon_history:
            self.config.icon_history.remove(text)
            save_config(self.config, self.config_path)

    def _on_mod_note_changed(self, unique_id: str, note: str):
        self.config.mod_notes[unique_id] = note
        save_config(self.config, self.config_path)

    def _on_version_meta_updated(self, version: GameVersion):
        if self.left_pane._selected_version and self.left_pane._selected_version.id == version.id:
            self.left_pane.set_selected_version(version)
        if self.right_pane.current_version and self.right_pane.current_version.id == version.id:
            self.right_pane.update_version_context(version)
        for i in range(self.right_pane.versions_list_layout.count()):
            item = self.right_pane.versions_list_layout.itemAt(i)
            if item and item.widget():
                w = item.widget()
                if isinstance(w, VersionListCard) and w.version.id == version.id:
                    w.update_ui()
                    break

        # 把版本概览里的图标历史同步进配置，避免只保留一个路径
        overview = self.right_pane.overview_page
        if hasattr(overview, "combo_icon"):
            history: List[str] = []
            for i in range(overview.combo_icon.fixed_items_count, overview.combo_icon.count()):
                item_text = overview.combo_icon.itemText(i)
                if item_text and item_text not in history:
                    history.append(item_text)
            if history != self.config.icon_history:
                self.config.icon_history = history
                save_config(self.config, self.config_path)

    def show_overview(self):
        ver = getattr(self.right_pane, "current_version", None)
        if ver:
            self.right_pane.overview_page.set_history(self.config.icon_history)
            self.right_pane.show_overview(ver)
        else:
            QtWidgets.QMessageBox.information(self, "提示", "当前未选定任何版本，无法打开版本概览。")

    def resizeEvent(self, event: QtGui.QResizeEvent):
        super().resizeEvent(event)
        if hasattr(self, 'overlay') and self.centralWidget():
            self.overlay.setGeometry(self.centralWidget().rect())
            self.bg_label.setGeometry(self.centralWidget().rect())
            self._update_background_geometry()
        if hasattr(self, "floating_gif"):
            self.floating_gif.update_anchor_position()

    def _update_background_geometry(self):
        target_size = self.centralWidget().rect().size()
        if not target_size.isValid() or target_size.width() <= 0: return

        if self._bg_original_pixmap and not self.bg_movie:
            orig = self._bg_original_pixmap
            scaled = orig.scaled(target_size, QtCore.Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                 QtCore.Qt.TransformationMode.SmoothTransformation)
            x = (scaled.width() - target_size.width()) // 2
            y = (scaled.height() - target_size.height()) // 2
            self.bg_label.setPixmap(scaled.copy(x, y, target_size.width(), target_size.height()))
        elif self.bg_movie and self._bg_movie_original_size.isValid():
            orig_size = self._bg_movie_original_size
            scale = max(target_size.width() / orig_size.width(), target_size.height() / orig_size.height())
            self.bg_movie.setScaledSize(QtCore.QSize(int(orig_size.width() * scale), int(orig_size.height() * scale)))

    def on_set_background_str(self, path_str: str):
        if is_preset(path_str):
            preset_name = path_str[len(PRESET_STR):]
            background_path = PRESET_BACKGROUNDS_PATHS.get(preset_name)
            if not (isinstance(background_path, Path) and background_path.exists()): background_path = None
        else:
            background_path = Path(path_str)
            if path_str not in self.config.bg_history:
                self.config.bg_history.insert(0, path_str)
                save_config(self.config, self.config_path)
        self.set_background(background_path)

    def set_background(self, path: Optional[Path]):
        if self.bg_movie:
            self.bg_movie.stop()
            self.bg_movie = None
        self._bg_original_pixmap = None

        if path is None or not path.exists():
            self.bg_label.clear()
            self.config.background_path = None
        else:
            if path.suffix.lower() == ".gif":
                reader = QtGui.QImageReader(str(path))
                self._bg_movie_original_size = reader.size()
                movie = QtGui.QMovie(str(path))
                movie.setCacheMode(QtGui.QMovie.CacheMode.CacheAll)
                movie.start()
                self.bg_label.setMovie(movie)
                self.bg_movie = movie
            else:
                self._bg_original_pixmap = QtGui.QPixmap(str(path))
            self.config.background_path = str(path)
            self._update_background_geometry()
        save_config(self.config, self.config_path)

    def refresh_versions(self):
        self._scanned_versions = scan_versions(self.game_root)
        while self.right_pane.versions_list_layout.count() > 1:
            i = self.right_pane.versions_list_layout.takeAt(0)
            if i.widget(): i.widget().deleteLater()

        last_ver = None
        for v in self._scanned_versions:
            if self.config.last_version_id and v.id == self.config.last_version_id: last_ver = v
            detail = self._create_version_detail_widget(v)
            self.right_pane.add_versions_list_row(detail)

        if last_ver:
            self.left_pane.set_selected_version(last_ver)
            self.right_pane.update_version_context(last_ver)
        else:
            self.left_pane.set_selected_version(None)
            self.right_pane.update_version_context(None)

    def _create_version_detail_widget(self, version: GameVersion) -> QtWidgets.QWidget:
        w = VersionListCard(version)
        w.clicked.connect(lambda: self._on_version_chosen(version, False))
        w.settings_clicked.connect(lambda: self._on_version_chosen(version, True))
        return w

    def _on_version_chosen(self, version: GameVersion, go_to_settings: bool):
        self.left_pane.set_selected_version(version)
        self.right_pane.update_version_context(version)
        self.config.last_version_id = version.id
        save_config(self.config, self.config_path)
        if go_to_settings:
            self.right_pane.show_settings()
        else:
            self.right_pane.show_empty()

    @QtCore.Slot(GameVersion)
    def on_launch_version(self, version: GameVersion):
        self.config.last_version_id = version.id
        save_config(self.config, self.config_path)

        # 按钮进入加载状态
        self.left_pane.btn_launch.setEnabled(False)
        self.left_pane.launch_label_main.setText("正在启动…")
        self.left_pane.launch_label_sub.setText(version.name)

        try:
            proc = launch_executable(version)
            if proc:
                QtCore.QTimer.singleShot(5000, self._reset_launch_button)
            else:
                QtWidgets.QMessageBox.critical(self, "错误", "未找到可执行文件。")
                self._reset_launch_button()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "启动失败", f"启动失败：{e}")
            self._reset_launch_button()

    def _reset_launch_button(self):
        self.left_pane.btn_launch.setEnabled(True)
        self.left_pane.launch_label_main.setText("启动游戏")
        # 保持当前版本提示
        if self.left_pane._selected_version:
            self.left_pane.launch_label_sub.setText(self.left_pane._selected_version.name)
        else:
            self.left_pane.launch_label_sub.setText("当前版本: 未选择")

    def show_versions_list(self):
        self.right_pane.show_versions()

    def show_settings(self):
        self.right_pane.show_settings()

    def show_mod_viewer(self):
        ver = self.right_pane.current_version
        if ver:
            decrypted_key = decrypt_api_key(getattr(self.config, "encrypt_nexus_api_key", ""))
            self.right_pane.show_mod_manager(ver, self.config.mod_notes, decrypted_key)

    def show_saves_list(self):
        def on_row_clicked(name, cfg=None, vers=None):
            if cfg is None:
                cfg = self.config
            if vers is None:
                vers = self._scanned_versions
            self.right_pane.show_save_detail(name, cfg, vers)

        self.right_pane.clear_saves_list()
        saves = scan_saves()
        for save_path in saves:
            save_name = save_path.name
            meta = self.config.saves.get(save_name, SaveMetadata())
            row = SaveRow(
                save_name,
                self._scanned_versions,
                meta.version_id,
                meta.note,
                meta.icon_path,
                meta.icon_source,
                meta.icon_version_id,
            )
            row.meta_changed.connect(self._on_save_meta_changed)
            row.clicked.connect(on_row_clicked)
            self.right_pane.add_save_row(row)
        self.right_pane.show_saves()

    @QtCore.Slot(str, str, str, str, str, str)
    def _on_save_meta_changed(self, save_name: str, version_id: str, note: str, icon_path: str, icon_source: str,
                              icon_version_id: str):
        if save_name not in self.config.saves:
            self.config.saves[save_name] = SaveMetadata()

        meta = self.config.saves[save_name]
        meta.version_id = version_id
        meta.note = note
        meta.icon_path = icon_path
        meta.icon_source = icon_source
        meta.icon_version_id = icon_version_id

        if version_id and icon_source in (ICON_SOURCE_NONE, ICON_SOURCE_VERSION):
            bound_icon = resolve_version_icon_path(version_id, self._scanned_versions)
            if bound_icon:
                meta.icon_path = bound_icon
                meta.icon_source = ICON_SOURCE_VERSION
                meta.icon_version_id = version_id
            else:
                meta.icon_path = ""
                meta.icon_source = ICON_SOURCE_NONE
                meta.icon_version_id = ""

        if not version_id and icon_source != ICON_SOURCE_CUSTOM:
            meta.icon_path = ""
            meta.icon_source = ICON_SOURCE_NONE
            meta.icon_version_id = ""

        save_config(self.config, self.config_path)
        self.show_saves_list()
        # if getattr(self.right_pane.save_detail_page, "save_name", "") == save_name:
        #     self.right_pane.show_save_detail(save_name, self.config, self._scanned_versions)

    @QtCore.Slot(str, str)
    def _on_save_icon_changed(self, save_name: str, icon_path: str):
        if save_name not in self.config.saves:
            self.config.saves[save_name] = SaveMetadata()

        meta = self.config.saves[save_name]
        meta.icon_path = icon_path
        meta.icon_source = ICON_SOURCE_CUSTOM if icon_path else ICON_SOURCE_NONE
        meta.icon_version_id = ""

        if icon_path and not is_preset(icon_path) and icon_path not in self.config.icon_history:
            self.config.icon_history.insert(0, icon_path)

        save_config(self.config, self.config_path)

        version_label = resolve_version_display_name(meta.version_id, self._scanned_versions)
        self.right_pane.save_detail_page.load_save(
            save_name,
            icon_path,
            self.config.icon_history,
            meta.version_id,
            meta.note,
            version_label,
        )

    @QtCore.Slot(str)
    def handle_save_backup(self, save_name: str):
        page = self.right_pane.save_detail_page
        page.set_backup_status("备份中...", False, "#3b82f6")
        QtCore.QTimer.singleShot(50, lambda: self._execute_backup(save_name, page))

    def _execute_backup(self, save_name: str, page: SaveDetailPage):
        if backup_save_folder(save_name):
            page.set_backup_status("备份成功!", False, "#10b981")
        else:
            page.set_backup_status("备份失败", False, "#ef4444")
        QtCore.QTimer.singleShot(2000, lambda: page.set_backup_status("备份存档", True, "#10b981"))

    @QtCore.Slot(str)
    def handle_save_delete(self, save_name: str):
        if DeleteConfirmDialog("删除存档",
                               f"确定要永久删除存档 <b>{save_name}</b> 吗？<br>",
                               self).exec() == QtWidgets.QDialog.DialogCode.Accepted:
            backup_save_folder(save_name)
            save_path = get_saves_directory() / save_name
            if save_path.exists(): shutil.rmtree(save_path, ignore_errors=True)
            if save_name in self.config.saves:
                del self.config.saves[save_name]
                save_config(self.config, self.config_path)
            self.show_saves_list()

    @QtCore.Slot(str)
    def _on_save_open_folder(self, save_name: str):
        save_path = get_saves_directory() / save_name
        if save_path.exists(): open_in_file_explorer(save_path)

    def on_open_current_folder(self):
        self.right_pane.btn_open_current_folder.setEnabled(False)

        ver = self.right_pane.current_version
        if ver and ver.base_dir.exists():
            open_in_file_explorer(ver.base_dir)

        QtCore.QTimer.singleShot(2000, lambda: self.right_pane.btn_open_current_folder.setEnabled(True))

    def on_open_saves_folder(self):
        self.right_pane.btn_open_saves_folder.setEnabled(False)

        saves_dir = get_saves_directory()
        if saves_dir.exists(): open_in_file_explorer(saves_dir)

        QtCore.QTimer.singleShot(2000, lambda: self.right_pane.btn_open_saves_folder.setEnabled(True))

    def show_add_api_dialog(self):
        def mask_key(key: str, prefix: int = 4, suffix: int = 4, mask: str = "****") -> str:
            if not key:
                return "请输入 API Key..."
            length = len(key)
            if length <= prefix + suffix:
                prefix = max(1, length // 3)
                suffix = max(1, length - prefix - 1)
            return f'目前: {key[:prefix] + mask + key[-suffix:]}'

        current_encrypt_api_key = getattr(self.config, "encrypt_nexus_api_key", "")
        current_api_key = decrypt_api_key(current_encrypt_api_key)
        display_api_key = mask_key(current_api_key) if current_api_key else "请输入 API Key..."
        dialog = ApiInputDialog(self, hint=display_api_key)
        if dialog.exec():
            value = dialog.get_value()
            # QtWidgets.QMessageBox.information(self, "提示", "API 已保存")

            if value.strip():
                if value == "clear":
                    self.config.encrypt_nexus_api_key = ""
                    save_config(self.config, self.config_path)
                    return
                self.config.encrypt_nexus_api_key = encrypt_api_key(value)
                save_config(self.config, self.config_path)

    def show_add_game_root(self):
        dialog = GameRootSelectDialog(is_has_version=bool(self._scanned_versions))
        if dialog.exec() != QtWidgets.QDialog.DialogCode.Accepted:
            return
        game_root = dialog.get_value()
        if not game_root:
            return
        self.config.game_root = str(game_root)
        save_config(self.config, self.config_path)
        self.game_root = game_root
        self.refresh_versions()

    def _load_state(self):
        while self.right_pane.combo_bg.count() > self.right_pane.combo_bg.fixed_items_count:
            self.right_pane.combo_bg.removeItem(self.right_pane.combo_bg.fixed_items_count)
        self.right_pane.combo_bg.load_history(self.config.bg_history)

        if self.config.background_path:
            p = Path(self.config.background_path)
            if p.exists():
                self.set_background(p)
                self.right_pane.combo_bg.push_to_top(str(p), is_history=True)

        geom = self.config.window_geometry or {}
        try:
            if geom.get("size"): self.resize(*geom["size"])
            if geom.get("pos"): self.move(*geom["pos"])
        except:
            pass

    def closeEvent(self, event: QtGui.QCloseEvent):
        if self.right_pane.current_version and self.right_pane.overview_page.combo_icon:
            icon_history = []
            for i in range(self.right_pane.overview_page.combo_icon.fixed_items_count,
                           self.right_pane.overview_page.combo_icon.count()):
                icon_history.append(self.right_pane.overview_page.combo_icon.itemText(i))
            self.config.icon_history = icon_history

        self.config.window_geometry = {"size": [self.width(), self.height()], "pos": [self.x(), self.y()]}
        save_config(self.config, self.config_path)
        super().closeEvent(event)


app = QtWidgets.QApplication(sys.argv)
tnt_sound = AudioPool(SOUNDS_PATH / "minecraft-explode1.wav")
tnt_sound.set_volume(0.8)
popup_sound = AudioPool(SOUNDS_PATH / "000000ea.wav")
junimo_sound = AudioPool(SOUNDS_PATH / "00000132.wav")
mc_firework_sound = AudioPool(SOUNDS_PATH / "minecraft_firework.wav") if IS_MY_BIRTHDAY else None

def main():
    config_path = BASE_DIR / CONFIG_FILENAME
    config = load_config(config_path)
    # QtCore.QCoreApplication.setAttribute(
    #     QtCore.Qt.ApplicationAttribute.AA_UseDesktopOpenGL
    # )

    update_launch_record()

    icon = QtGui.QIcon(str(IMAGES_PATH / "icon.ico"))
    app.setWindowIcon(icon)
    app.setStyleSheet("""
        QPushButton {
            cursor: pointer; /* 鼠标悬浮时显示手型光标 */
        }
        QPushButton:focus {
            outline: none;
        }
    """)
    app.styleHints().setColorScheme(QtCore.Qt.ColorScheme.Light)

    game_root = find_game_root(config)
    if game_root is None:
        dialog = GameRootSelectDialog()
        if dialog.exec() != QtWidgets.QDialog.DialogCode.Accepted:
            return
        game_root = dialog.get_value()
        if not game_root:
            return
        config.game_root = str(game_root)
        save_config(config, config_path)
    else:
        config.game_root = str(game_root)
        save_config(config, config_path)

    window = LauncherMainWindow(game_root=game_root, config_path=config_path)
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
