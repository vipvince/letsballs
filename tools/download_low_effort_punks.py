#!/usr/bin/env python3
"""Download all Low Effort Punks NFT images from OpenSea into a local folder.

Uses OpenSea's public GraphQL endpoint (no API key) to list every item in
https://opensea.io/collection/low-effort-punks, then downloads each image
named by its collection token id (the number in \"low effort punk N\").

Example:
  python3 tools/download_low_effort_punks.py
  python3 tools/download_low_effort_punks.py --out \"lw effort punks\" --workers 24
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

COLLECTION_SLUG = "low-effort-punks"
GQL_URL = "https://gql.opensea.io/graphql"
DEFAULT_OUT = "lw effort punks"
EXPECTED_COUNT = 10021
# Official names plus the known collection typo ("lwo effort punk 520").
NAME_RE = re.compile(r"(?:low|lwo) effort punk\s+(\d+)\s*$", re.I)
NON_ALNUM_RE = re.compile(r"[^a-zA-Z0-9._-]+")

LIST_QUERY = """
query CollectionItems($slug: String!, $cursor: String, $limit: Int!) {
  collectionItems(
    collectionSlug: $slug
    sort: { by: CREATED_DATE, direction: ASC }
    limit: $limit
    cursor: $cursor
  ) {
    items {
      tokenId
      name
      imageUrl
      tokenUri
    }
    nextPageCursor
  }
}
"""


def _gql(query: str, variables: dict, retries: int = 6) -> dict:
    payload = json.dumps({"query": query, "variables": variables}).encode()
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "x-app-id": "opensea-web",
        "User-Agent": "Mozilla/5.0 (compatible; lep-downloader/1.0)",
        "Origin": "https://opensea.io",
        "Referer": f"https://opensea.io/collection/{COLLECTION_SLUG}",
    }
    last_err: Exception | None = None
    for attempt in range(retries):
        req = urllib.request.Request(GQL_URL, data=payload, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = json.loads(resp.read().decode())
            if data.get("errors"):
                msg = data["errors"][0].get("message", str(data["errors"]))
                raise RuntimeError(f"GraphQL error: {msg}")
            return data["data"]
        except Exception as exc:  # noqa: BLE001 - retry network/API blips
            last_err = exc
            time.sleep(min(2**attempt, 20))
    raise RuntimeError(f"GraphQL request failed after retries: {last_err}")


def list_all_items(limit: int = 100, pause: float = 0.15) -> list[dict]:
    items: list[dict] = []
    cursor = None
    page = 0
    while True:
        data = _gql(
            LIST_QUERY,
            {"slug": COLLECTION_SLUG, "cursor": cursor, "limit": limit},
        )
        conn = data["collectionItems"]
        batch = conn.get("items") or []
        items.extend(batch)
        page += 1
        cursor = conn.get("nextPageCursor")
        print(f"listed page {page}: +{len(batch)} (total {len(items)})", flush=True)
        if not cursor or not batch:
            break
        time.sleep(pause)
    return items


def punk_id_from_name(name: str | None) -> int | None:
    if not name:
        return None
    m = NAME_RE.search(name.strip())
    return int(m.group(1)) if m else None


def normalize_image_url(url: str) -> str:
    """Prefer a full-size CDN URL when OpenSea appends resize query params."""
    if not url:
        return url
    # Drop resize hints so we get the source asset when possible.
    if "?" in url:
        base, _, _qs = url.partition("?")
        url = base
    # i2c negotiates AVIF by default; raw2 serves the original PNG.
    if url.startswith("https://i2c.seadn.io/"):
        url = "https://raw2.seadn.io/" + url[len("https://i2c.seadn.io/") :]
    elif url.startswith("https://i.seadn.io/"):
        url = "https://raw2.seadn.io/" + url[len("https://i.seadn.io/") :]
    return url


def _sniff_image_suffix(data: bytes, ctype: str) -> str:
    if data.startswith(b"\x89PNG\r\n\x1a\n"):
        return ".png"
    if data[:3] == b"\xff\xd8\xff":
        return ".jpg"
    if data[:4] == b"GIF8":
        return ".gif"
    if len(data) >= 12 and data[0:4] == b"RIFF" and data[8:12] == b"WEBP":
        return ".webp"
    if len(data) >= 12 and data[4:8] == b"ftyp" and b"avif" in data[8:20]:
        return ".avif"
    ctype = (ctype or "").lower()
    if "jpeg" in ctype or "jpg" in ctype:
        return ".jpg"
    if "webp" in ctype:
        return ".webp"
    if "gif" in ctype:
        return ".gif"
    if "avif" in ctype:
        return ".avif"
    return ".png"


def download_one(
    url: str,
    dest: Path,
    retries: int = 5,
    force: bool = False,
) -> tuple[str, bool, str]:
    if (
        not force
        and dest.exists()
        and dest.stat().st_size > 0
        and dest.read_bytes()[:8] == b"\x89PNG\r\n\x1a\n"
    ):
        return (dest.name, True, "skip")
    headers = {
        "User-Agent": "Mozilla/5.0 (compatible; lep-downloader/1.0)",
        "Referer": "https://opensea.io/",
        # Exact Accept matters: broader image/* makes seadn return AVIF.
        "Accept": "image/png",
    }
    last = ""
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = resp.read()
                ctype = (resp.headers.get("Content-Type") or "").lower()
            if not data:
                raise RuntimeError("empty body")
            suffix = _sniff_image_suffix(data, ctype)
            dest.parent.mkdir(parents=True, exist_ok=True)
            # Prefer PNG on disk. Some seadn hosts still return AVIF bodies.
            if suffix == ".avif":
                avif_tmp = dest.with_suffix(".avif.part")
                avif_tmp.write_bytes(data)
                png_tmp = dest.with_suffix(".png.part")
                conv = subprocess.run(
                    ["ffmpeg", "-y", "-i", str(avif_tmp), str(png_tmp)],
                    capture_output=True,
                    text=True,
                )
                avif_tmp.unlink(missing_ok=True)
                if conv.returncode != 0 or not png_tmp.exists():
                    raise RuntimeError(
                        f"avif->png conversion failed: {conv.stderr[-200:]}"
                    )
                dest = dest.with_suffix(".png")
                png_tmp.replace(dest)
            else:
                dest = dest.with_suffix(suffix)
                tmp = dest.with_suffix(dest.suffix + ".part")
                tmp.write_bytes(data)
                tmp.replace(dest)
            return (dest.name, True, "ok")
        except Exception as exc:  # noqa: BLE001
            last = str(exc)
            time.sleep(min(1.5**attempt, 15))
    return (dest.name, False, last)


def _label_for_item(name: str | None, opensea_token_id: str, used: set[str]) -> str:
    """Return a filesystem label for one NFT (token id when available)."""
    punk_id = punk_id_from_name(name)
    if punk_id is not None:
        base = str(punk_id)
    else:
        slug = NON_ALNUM_RE.sub("_", (name or "unknown").strip()).strip("_")
        base = slug or f"token_{opensea_token_id[-12:]}"

    label = base
    if label in used:
        # Keep every OpenSea item (collection has duplicate display names).
        label = f"{base}__{opensea_token_id[-10:]}"
    used.add(label)
    return label


def build_manifest(raw_items: list[dict]) -> list[dict]:
    """Build one manifest row per OpenSea item (all 10021)."""
    manifest: list[dict] = []
    used_labels: set[str] = set()
    for item in raw_items:
        image_url = normalize_image_url(item.get("imageUrl") or "")
        if not image_url:
            continue
        opensea_token_id = str(item.get("tokenId") or "")
        name = item.get("name")
        punk_id = punk_id_from_name(name)
        label = _label_for_item(name, opensea_token_id, used_labels)
        manifest.append(
            {
                "label": label,
                "token_id": punk_id,
                "name": name,
                "opensea_token_id": opensea_token_id,
                "image_url": image_url,
                "token_uri": item.get("tokenUri"),
            }
        )
    manifest.sort(
        key=lambda x: (
            x["token_id"] is None,
            x["token_id"] if x["token_id"] is not None else 10**12,
            x["label"],
        )
    )
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=DEFAULT_OUT,
        help=f'output folder (default: "{DEFAULT_OUT}")',
    )
    parser.add_argument("--workers", type=int, default=20, help="parallel downloads")
    parser.add_argument(
        "--manifest-only",
        action="store_true",
        help="only write manifest.json, skip image downloads",
    )
    parser.add_argument(
        "--resume-manifest",
        action="store_true",
        help="reuse existing manifest.json in the output folder",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="re-download even when an output file already exists",
    )
    args = parser.parse_args()

    out_dir = Path(args.out)
    if not out_dir.is_absolute():
        out_dir = Path.cwd() / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = out_dir / "manifest.json"

    if args.resume_manifest and manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        print(f"loaded manifest: {len(manifest)} items from {manifest_path}")
        # Re-normalize URLs in case an older manifest pointed at i2c AVIF endpoints.
        for row in manifest:
            row["image_url"] = normalize_image_url(row.get("image_url") or "")
        manifest_path.write_text(json.dumps(manifest, indent=2))
    else:
        print(f"listing collection `{COLLECTION_SLUG}` via OpenSea GraphQL…")
        raw = list_all_items()
        manifest = build_manifest(raw)
        manifest_path.write_text(json.dumps(manifest, indent=2))
        print(f"wrote {manifest_path} ({len(manifest)} items)")
        if len(manifest) != EXPECTED_COUNT:
            print(
                f"warning: expected ~{EXPECTED_COUNT} items, got {len(manifest)}",
                file=sys.stderr,
            )

    if args.manifest_only:
        return 0

    jobs = []
    for row in manifest:
        label = row["label"]
        # Label files with the collection token id from the NFT name.
        dest = out_dir / f"{label}.png"
        jobs.append((row["image_url"], dest, label))

    ok = skip = fail = 0
    failures: list[tuple[str, str]] = []
    print(f"downloading {len(jobs)} images into {out_dir} with {args.workers} workers…")
    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        futs = {
            pool.submit(download_one, url, dest, 5, args.force): label
            for url, dest, label in jobs
        }
        done = 0
        for fut in as_completed(futs):
            label = futs[fut]
            done += 1
            _name, success, status = fut.result()
            if success and status == "skip":
                skip += 1
            elif success:
                ok += 1
            else:
                fail += 1
                failures.append((label, status))
            if done % 250 == 0 or done == len(futs):
                print(
                    f"progress {done}/{len(futs)}  saved={ok} skipped={skip} failed={fail}",
                    flush=True,
                )

    if failures:
        fail_path = out_dir / "failures.json"
        fail_path.write_text(
            json.dumps([{"label": t, "error": e} for t, e in failures], indent=2)
        )
        print(f"wrote {fail_path} ({len(failures)} failures)")

    pngs = list(out_dir.glob("*.png"))
    print(
        f"done. images_on_disk={len(pngs)} saved={ok} skipped={skip} failed={fail} dir={out_dir}"
    )
    return 1 if fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
