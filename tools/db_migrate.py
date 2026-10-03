"""
Export local SQLite / import into whatever DB app.py uses (Turso when secrets set).

Usage (from repo root):
  python tools/db_migrate.py export
  python tools/db_migrate.py seed-games          # restore known Oct games into current DB
  python tools/db_migrate.py import path.json   # after Turso secrets are configured
  python tools/db_migrate.py status
"""
from __future__ import annotations

import argparse
import json
import os
import sqlite3
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
os.chdir(ROOT)

LOCAL_DB = ROOT / "tennis.db"
EXPORT_PATH = ROOT / "db_export_local.json"

# Reconstructed from live board before Cloud wipe (user chat / admin board)
KNOWN_GAMES = [
    {
        "when_text": "Oct 3 (Saturday) @ 6pm",
        "location": "Happy Valley",
        "spots": 2,
        "notes": "",
        "created_by": "vip",
    },
    {
        "when_text": "Oct 10 (Saturday) @ 11am",
        "location": "Happy Valley",
        "spots": 2,
        "notes": "",
        "created_by": "vip",
    },
]


def _load_app():
    import app as app_mod

    return app_mod


def cmd_status(_: argparse.Namespace) -> None:
    app = _load_app()
    url, token = app.turso_creds()
    print("durable (Turso secrets present):", app.using_durable_db())
    print("TURSO_DATABASE_URL:", "set" if url else "missing")
    print("TURSO_AUTH_TOKEN:", "set" if token else "missing")
    print("local tennis.db:", LOCAL_DB.exists(), LOCAL_DB)
    if LOCAL_DB.exists():
        con = sqlite3.connect(LOCAL_DB)
        for t in ("users", "games", "game_signups"):
            try:
                n = con.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
                print(f"  local {t}: {n}")
            except Exception:
                print(f"  local {t}: (missing)")
        con.close()
    app.init_db()
    with app.get_conn() as conn:
        for t in ("users", "games", "game_signups"):
            try:
                n = conn.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
                # libsql may return tuple or dict-like
                if isinstance(n, (tuple, list)):
                    n = n[0]
                elif isinstance(n, dict):
                    n = list(n.values())[0]
                print(f"  active {t}: {n}")
            except Exception as e:
                print(f"  active {t}: error {e}")


def cmd_export(_: argparse.Namespace) -> None:
    if not LOCAL_DB.exists():
        raise SystemExit(f"No local DB at {LOCAL_DB}")
    con = sqlite3.connect(LOCAL_DB)
    con.row_factory = sqlite3.Row
    payload = {
        "source": str(LOCAL_DB),
        "users": [dict(r) for r in con.execute("SELECT * FROM users")],
        "games": [dict(r) for r in con.execute("SELECT * FROM games")],
        "game_signups": [],
    }
    try:
        payload["game_signups"] = [dict(r) for r in con.execute("SELECT * FROM game_signups")]
    except Exception:
        pass
    con.close()
    EXPORT_PATH.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8",
    )
    print(
        f"Exported {len(payload['users'])} users, "
        f"{len(payload['games'])} games, "
        f"{len(payload['game_signups'])} signups → {EXPORT_PATH}"
    )
    print("NOTE: local snapshot has no games (last write ~Sept 30). Cloud wipe is not recoverable from disk.")


def _upsert_user(app, conn, u: dict) -> None:
    handle = app.normalize_handle(u.get("ig_handle") or "")
    if not handle:
        return
    cols = [
        "ig_handle",
        "pin_hash",
        "animal",
        "vibe",
        "animal_emoji",
        "mascot",
        "avatar_path",
        "ig_photo_path",
        "gender",
        "nationality",
        "age_guess",
        "ai_enabled",
        "gate_override",
        "gate_detail",
        "assign_why",
        "invite_score",
        "invite_score_override",
        "lang",
    ]
    vals = {c: u.get(c) for c in cols}
    vals["ig_handle"] = handle
    existing = conn.execute(
        "SELECT id FROM users WHERE lower(ig_handle) = ?",
        [handle],
    ).fetchone()
    ex = app._as_dict(existing)
    if ex.get("id") is not None:
        sets = ", ".join(f"{c} = ?" for c in cols if c != "ig_handle")
        conn.execute(
            f"UPDATE users SET {sets} WHERE id = ?",
            [vals[c] for c in cols if c != "ig_handle"] + [ex["id"]],
        )
    else:
        conn.execute(
            f"INSERT INTO users ({', '.join(cols)}) VALUES ({', '.join('?' for _ in cols)})",
            [vals[c] for c in cols],
        )


def cmd_import(ns: argparse.Namespace) -> None:
    path = Path(ns.path or EXPORT_PATH)
    if not path.is_file():
        raise SystemExit(f"Missing export file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    app = _load_app()
    if not app.using_durable_db():
        print(
            "WARNING: Turso secrets not detected — import will write to local/active SQLite.\n"
            "Set TURSO_DATABASE_URL + TURSO_AUTH_TOKEN (env or Streamlit secrets) first for durable migrate."
        )
    app.init_db()
    with app.get_conn() as conn:
        for u in payload.get("users") or []:
            _upsert_user(app, conn, u)
        # Games: insert if no matching when_text+location
        for g in payload.get("games") or []:
            when = (g.get("when_text") or "").strip()
            loc = (g.get("location") or "").strip()
            if not when:
                continue
            prior = conn.execute(
                "SELECT id FROM games WHERE when_text = ? AND COALESCE(location,'') = ?",
                [when, loc],
            ).fetchone()
            if app._as_dict(prior).get("id") is not None:
                continue
            conn.execute(
                """
                INSERT INTO games (when_text, location, spots, notes, created_by)
                VALUES (?, ?, ?, ?, ?)
                """,
                [
                    when,
                    loc,
                    int(g.get("spots") or 2),
                    (g.get("notes") or "").strip(),
                    app.normalize_handle(g.get("created_by") or "vip") or "vip",
                ],
            )
        # Signups best-effort by handle + game when_text if ids differ
        for s in payload.get("game_signups") or []:
            handle = app.normalize_handle(s.get("ig_handle") or "")
            gid = s.get("game_id")
            if not handle or gid is None:
                continue
            try:
                conn.execute(
                    "INSERT OR IGNORE INTO game_signups (game_id, ig_handle, admin_seen) VALUES (?, ?, ?)",
                    [int(gid), handle, int(s.get("admin_seen") or 0)],
                )
            except Exception:
                pass
        if hasattr(conn, "_shared") and conn._shared is not None:
            conn._shared["dirty"] = True
    print(f"Imported from {path} into active DB (durable={app.using_durable_db()})")


def cmd_seed_games(_: argparse.Namespace) -> None:
    app = _load_app()
    app.init_db()
    added = 0
    with app.get_conn() as conn:
        for g in KNOWN_GAMES:
            when = g["when_text"]
            loc = g["location"]
            prior = conn.execute(
                "SELECT id FROM games WHERE when_text = ? AND COALESCE(location,'') = ?",
                [when, loc],
            ).fetchone()
            if app._as_dict(prior).get("id") is not None:
                print("skip existing:", when)
                continue
            # spots = open spots after creator auto-join convention in insert_game
            # Here we insert open spots directly (2 left as on the old board)
            conn.execute(
                """
                INSERT INTO games (when_text, location, spots, notes, created_by)
                VALUES (?, ?, ?, ?, ?)
                """,
                [when, loc, int(g["spots"]), g.get("notes") or "", g["created_by"]],
            )
            gid_row = conn.execute("SELECT last_insert_rowid() AS id").fetchone()
            gid = app._as_dict(gid_row).get("id")
            if gid is None and isinstance(gid_row, (tuple, list)):
                gid = gid_row[0]
            try:
                conn.execute(
                    "INSERT OR IGNORE INTO game_signups (game_id, ig_handle, admin_seen) VALUES (?, ?, 1)",
                    [int(gid), g["created_by"]],
                )
            except Exception:
                pass
            added += 1
            print("added:", when, "id", gid)
        if hasattr(conn, "_shared") and conn._shared is not None:
            conn._shared["dirty"] = True
    print(f"seed-games done (+{added}). durable={app.using_durable_db()}")


def main() -> None:
    p = argparse.ArgumentParser(description="Export/import club DB toward Turso")
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status", help="Show local vs Turso / active counts")
    sub.add_parser("export", help="Export local tennis.db → db_export_local.json")
    imp = sub.add_parser("import", help="Import JSON into active DB")
    imp.add_argument("path", nargs="?", default=str(EXPORT_PATH))
    sub.add_parser("seed-games", help="Re-add known Oct Happy Valley games")
    ns = p.parse_args()
    {
        "status": cmd_status,
        "export": cmd_export,
        "import": cmd_import,
        "seed-games": cmd_seed_games,
    }[ns.cmd](ns)


if __name__ == "__main__":
    main()
