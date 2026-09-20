"""Generate missing avatar PNGs as cute stylized portraits (local, no API tokens)."""
from __future__ import annotations

import json
import os
import random
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent
AVATAR_DIR = ROOT / "avatars"
EXTRA = ROOT / "avatar_pool_extra.json"

PALETTES = [
    ((34, 139, 80), (250, 240, 180)),
    ((20, 90, 60), (180, 230, 200)),
    ((60, 40, 90), (230, 200, 255)),
    ((20, 60, 110), (180, 220, 255)),
    ((120, 50, 40), (255, 210, 180)),
    ((40, 40, 40), (220, 220, 220)),
    ((90, 60, 20), (255, 230, 160)),
    ((30, 100, 120), (180, 255, 240)),
    ((90, 30, 70), (255, 200, 230)),
    ((20, 80, 40), (200, 255, 160)),
]


def load_font(size: int) -> ImageFont.ImageFont:
    for path in (
        r"C:\Windows\Fonts\seguiemj.ttf",
        r"C:\Windows\Fonts\SegoeUIEmoji.ttf",
        r"C:\Windows\Fonts\arial.ttf",
    ):
        if os.path.isfile(path):
            try:
                return ImageFont.truetype(path, size=size)
            except Exception:
                continue
    return ImageFont.load_default()


def make_avatar(path: Path, emoji: str, label: str, seed: str) -> None:
    rng = random.Random(seed)
    c1, c2 = PALETTES[rng.randrange(len(PALETTES))]
    size = 512
    top = Image.new("RGB", (size, size), c1)
    bottom = Image.new("RGB", (size, size), c2)
    # vertical blend
    img = Image.blend(top, bottom, 0.45)
    # add a second diagonal wash via mask
    wash = Image.new("L", (size, size))
    wd = ImageDraw.Draw(wash)
    for y in range(size):
        wd.line([(0, y), (size, y)], fill=int(255 * y / size))
    img = Image.composite(bottom, top, wash)

    draw = ImageDraw.Draw(img)
    # court-ish circle stage
    overlay = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    od = ImageDraw.Draw(overlay)
    od.ellipse([70, 70, size - 70, size - 70], fill=(255, 255, 255, 70))
    # tiny tennis ball accent
    od.ellipse([size - 120, 40, size - 40, 120], fill=(210, 255, 90, 200))
    img = Image.alpha_composite(img.convert("RGBA"), overlay).convert("RGB")
    draw = ImageDraw.Draw(img)

    font_emoji = load_font(200)
    font_label = load_font(28)
    em = emoji or "🎾"
    bbox = draw.textbbox((0, 0), em, font=font_emoji)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
    try:
        draw.text(((size - tw) / 2, (size - th) / 2 - 36), em, font=font_emoji, embedded_color=True)
    except TypeError:
        draw.text(((size - tw) / 2, (size - th) / 2 - 36), em, font=font_emoji, fill=(20, 53, 37))

    text = (label or path.stem.replace("_", " "))[:26]
    bbox = draw.textbbox((0, 0), text, font=font_label)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
    pad_x, pad_y = 14, 10
    y0 = size - 88
    x0 = max(16, (size - tw) / 2)
    draw.rounded_rectangle(
        [x0 - pad_x, y0 - pad_y, x0 + tw + pad_x, y0 + th + pad_y],
        radius=18,
        fill=(20, 53, 37),
    )
    draw.text((x0, y0), text, font=font_label, fill=(232, 245, 238))

    path.parent.mkdir(parents=True, exist_ok=True)
    img.save(path, "PNG", optimize=True)


def main() -> None:
    rows = json.loads(EXTRA.read_text(encoding="utf-8"))
    made = skipped = 0
    for row in rows:
        fname = row.get("file")
        if not fname:
            continue
        out = AVATAR_DIR / fname
        if out.is_file() and out.stat().st_size > 1000:
            skipped += 1
            continue
        make_avatar(out, row.get("emoji") or "🎾", row.get("label") or fname, seed=fname)
        made += 1
        print("made", fname)
    print(f"done made={made} skipped={skipped} total_extra={len(rows)}")


if __name__ == "__main__":
    main()
