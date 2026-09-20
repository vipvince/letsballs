"""Check gate IN/OUT for four handles."""
import json
import os

import app

os.environ.setdefault("FACEPP_API_BASE", "https://api-us.faceplusplus.com/facepp/v3")

HANDLES = ["aiiiiiiyc", "oh.my.vian", "kkkkkkchow", "pkbtran"]

print(f"{'handle':<16} {'gate':<6} {'gender':<8} {'nat':<14} {'age':<14} photo feed")
print("-" * 90)

for h in HANDLES:
    try:
        research = app.research_handle_before_ig(h)
        scrape = app.scrape_instagram_bio(h, pre_web=research, skip_web=True)
        demo = app.infer_demographics(
            scrape.get("text") or "",
            scrape=scrape,
            handle=h,
            ig_photo_path=scrape.get("ig_photo_path") or "",
        )
        if (demo.get("nationality") or "unknown") == "unknown":
            fn = (demo.get("first_name") or "").lower().replace(" ", "")
            toks = set(app._handle_name_tokens(h))
            if fn in app._FEM_GIVEN or any(
                t in app._FEM_GIVEN or t in app._CJK_SURNAMES for t in toks
            ):
                demo["nationality"] = "Hong Kong"
        eligible, reason = app.club_ai_eligible(demo)
        gate = "IN" if eligible else "GATED"
        feed = len(scrape.get("ig_feed_paths") or [])
        line = (
            f"{h:<16} {gate:<6} {(demo.get('gender') or '?'):<8} "
            f"{(demo.get('nationality') or '?'):<14} {(demo.get('age_guess') or '?'):<14} "
            f"{demo.get('photo_ok')}/{demo.get('vision_photos')} f={feed}"
        )
        print(line.encode("ascii", "replace").decode("ascii"))
        if not eligible:
            print(f"  reason: {reason}")
        print(f"  vis={scrape.get('visibility')} name={demo.get('name_display') or ''}")
        print(f"  note={(demo.get('photo_note') or '')[:80]}")
    except Exception as exc:
        print(f"{h:<16} ERR {type(exc).__name__}: {exc}")

print("DONE")
