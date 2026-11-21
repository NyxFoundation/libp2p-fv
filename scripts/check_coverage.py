#!/usr/bin/env python3
"""Validate the obligation ledger without promoting model evidence to spec proof."""
import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATUSES = {"kernel-model", "external-contract", "unmodeled", "out-of-scope", "disabled", "tested-policy"}


def inventory_ids(root=ROOT):
    ids = []
    for path in sorted((root / "docs/properties").glob("*.md")):
        ids.extend(re.findall(r"^\| ([A-Z]-\d{2}\.\d{2}) \|", path.read_text(), re.M))
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate child IDs in the inventory")
    return set(ids)


def validate_ledger(data, root=ROOT):
    rows = data["obligations"]
    ids = [row["id"] for row in rows]
    if data["inventory_children"] != len(inventory_ids(root)):
        raise ValueError("inventory count metadata is stale")
    if len(ids) != len(set(ids)) or set(ids) != inventory_ids(root):
        raise ValueError("ledger IDs must match the inventory exactly, without duplicates")
    for row in rows:
        if row["status"] not in STATUSES or not isinstance(row["limitation"], str) or not row["limitation"].strip():
            raise ValueError(f"invalid status or missing boundary: {row['id']}")
        if row["status"] in {"kernel-model", "tested-policy"}:
            path, separator, symbol = row.get("artifact", "").partition("#")
            target = (root / path).resolve()
            if not target.is_relative_to((root / "Libp2p").resolve()):
                raise ValueError(f"artifact escapes the model directory: {row['id']}")
            if not separator or not symbol or target.suffix != ".lean" or not target.is_file():
                raise ValueError(f"missing model artifact: {row['id']}")
            if symbol not in (root / path).read_text():
                raise ValueError(f"missing model symbol: {row['id']}")
    return Counter(row["status"] for row in rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true",
                        help="fail on unmodeled/test-only entries; does not prove specification correspondence")
    args = parser.parse_args()
    try:
        counts = validate_ledger(json.loads((ROOT / "verification/coverage.json").read_text()))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"Invalid coverage ledger ({type(error).__name__}).\n")
    print("Coverage ledger:", ", ".join(f"{key}={counts[key]}" for key in sorted(STATUSES)))
    print("kernel-model means a model projection, not discharge of all inventory dependencies.")
    if args.require_complete and (counts["unmodeled"] or counts["tested-policy"]):
        parser.exit(1, "Incomplete libp2p scope: unmodeled or test-only obligations remain.\n")


if __name__ == "__main__":
    main()
