#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["ijson>=3.3,<4"]
# ///
"""Transport and stream exported CI metrics bundles. See .agents/skills/ci-metrics/collecting.md.

Collect and export with ci_metrics.py fetch/bundle; this utility makes no
network requests. The bundle preserves the original planning snapshots.
"""

import argparse
from collections import Counter
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

BLOCK = 1024 * 1024


def positive(value):
    result = float(value)
    if not math.isfinite(result) or result <= 0:
        raise argparse.ArgumentTypeError("must be a positive finite number")
    return result


def split(source, directory, part_bytes):
    """Split the compressed bytes, with a manifest written only on completion."""
    if part_bytes < 1:
        raise ValueError("part size must be at least one byte")
    directory.mkdir()  # Refuse to mix with an earlier or incomplete upload.
    parts, total, size = [], hashlib.sha256(), 0
    with source.open("rb") as stream:
        while True:
            block = stream.read(min(BLOCK, part_bytes))
            if not block:
                break
            name = f"{source.name}.part{len(parts):03d}"
            digest, count = hashlib.sha256(), 0
            with (directory / name).open("xb") as part:
                while block:
                    part.write(block)
                    digest.update(block)
                    total.update(block)
                    count += len(block)
                    if count == part_bytes:
                        break
                    block = stream.read(min(BLOCK, part_bytes - count))
            parts.append({"name": name, "size": count, "sha256": digest.hexdigest()})
            size += count
    if not parts:
        raise ValueError("cannot split an empty file")
    manifest = {"version": 1, "file": source.name, "size": size, "sha256": total.hexdigest(), "parts": parts}
    path = directory / "manifest.json"
    path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Upload {path} and all {len(parts)} parts in {directory}", file=sys.stderr)


def join(manifest_path, output):
    """Verify every part and the reconstructed compressed file before keeping it."""
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("version") != 1 or not manifest.get("parts"):
        raise ValueError("unsupported or empty split manifest")
    name = manifest["file"]
    if not isinstance(name, str) or name in ("", ".", "..") or "/" in name or "\\" in name or ":" in name:
        raise ValueError("manifest file must be a basename")
    # Match generated names, rather than treating uploaded paths as filesystem authority.
    for index, part in enumerate(manifest["parts"]):
        if part["name"] != f"{name}.part{index:03d}":
            raise ValueError("parts must have their original names and order")
    total, size = hashlib.sha256(), 0
    target = output.open("xb")
    try:
        with target:
            for part in manifest["parts"]:
                digest, count = hashlib.sha256(), 0
                with (manifest_path.parent / part["name"]).open("rb") as stream:
                    while block := stream.read(BLOCK):
                        digest.update(block)
                        total.update(block)
                        target.write(block)
                        count += len(block)
                if count != part["size"] or digest.hexdigest() != part["sha256"]:
                    raise ValueError(f"Size/checksum mismatch: {part['name']}")
                size += count
            if size != manifest["size"] or total.hexdigest() != manifest["sha256"]:
                raise ValueError("Reassembled file size/checksum mismatch")
    except BaseException:
        output.unlink(missing_ok=True)
        raise
    print(f"Verified {output} ({size} bytes)", file=sys.stderr)


def records(path):
    """Yield (kind, value), keeping only one runs/missing/errors entry in memory.

    Accept the original session's unversioned bundle as well as version 1.
    Artifacts can contain tens of MB of planning inputs; do not json.load the
    entire bundle. ijson is installed automatically by uv's script metadata.
    """
    import ijson

    opener = gzip.open if path.suffix == ".gz" else open
    builder = None
    depth = 0
    root = seen_runs = False
    with opener(path, "rb") as stream:
        try:
            for prefix, event, value in ijson.parse(stream, use_float=True):
                if not root:
                    if prefix != "" or event != "start_map":
                        raise ValueError("expected a metrics bundle object")
                    root = True
                if prefix == "runs" and event == "start_array":
                    seen_runs = True
                if builder is None:
                    if prefix in ("runs.item", "missing.item", "errors.item") and event == "start_map":
                        kind = prefix.split(".")[0]
                        builder = ijson.ObjectBuilder()
                    elif "." not in prefix and prefix and event in ("string", "number", "boolean", "null"):
                        yield prefix, value
                        continue
                    else:
                        continue
                builder.event(event, value)
                depth += (event in ("start_map", "start_array")) - (event in ("end_map", "end_array"))
                if depth == 0:
                    yield kind, builder.value
                    builder = None
        except ijson.JSONError as error:
            raise ValueError(f"invalid or truncated bundle JSON: {error}") from error
    if not seen_runs:
        raise ValueError("expected a bundle with a runs array, not an individual ci-metrics document")


def summary(path):
    """Coverage first, then small per-artifact rows, leaving raw data untouched."""
    result = {"artifacts": 0, "missing": [], "errors": [], "runs": []}
    conclusions, ids = Counter(), set()
    for kind, value in records(path):
        if kind != "runs":
            if kind == "schema_version" and value != 1:
                raise ValueError(f"unsupported bundle schema: {value}")
            if kind in ("missing", "errors"):
                result[kind].append(value)
            elif kind in ("schema_version", "repository", "workflow", "start", "end",
                           "window_basis", "downloaded_at", "inspected_runs", "limit", "selection_complete"):
                result[kind] = value
            continue
        run = value["run"]
        ids.add(run["id"])
        result["artifacts"] += 1
        conclusions[run.get("conclusion") or run.get("status") or "unknown"] += 1
        for name, metrics in value["files"].items():
            if not isinstance(metrics, dict):
                continue
            lean = metrics.get("lean", {})
            built = [times for job in lean.get("jobs", []) for times in job.get("built", {}).values()]
            result["runs"].append({"run": run, "artifact_id": value["artifact_id"], "file": name,
                                   "metrics_run": metrics.get("run"), "collection": metrics.get("collection"),
                                   "planning_status": lean.get("planning", {}).get("status", "not_collected"),
                                   "missing_logs": lean.get("missing_logs", []),
                                   "module_build_observations": sum(len(t) for t in built),
                                   "summed_module_seconds": sum(sum(t.values()) for t in built),
                                   "jobs": [{k: j.get(k) for k in
                                             ("id", "name", "status", "conclusion", "queued_s", "duration_s")}
                                            for j in metrics.get("jobs", [])]})
    result["unique_runs_with_artifacts"] = len(ids)
    result["artifact_conclusions"] = dict(conclusions)
    result["duration_basis"] = "module observations may repeat across shards; summed module seconds are not elapsed time"
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    chunks = commands.add_parser("split", help="prepare compressed bytes for attachment limits")
    chunks.add_argument("source", type=Path)
    chunks.add_argument("--directory", type=Path, required=True, help="new directory for manifest and parts")
    chunks.add_argument("--part-mib", type=positive, default=24, help="part size in MiB (default: 24)")
    assemble = commands.add_parser("join", help="verify and reassemble downloaded attachments")
    assemble.add_argument("manifest", type=Path)
    assemble.add_argument("--output", type=Path, required=True)
    inspect = commands.add_parser("summary", help="stream a bundle to a smaller JSON summary on stdout")
    inspect.add_argument("bundle", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "split":
            split(args.source, args.directory, int(args.part_mib * BLOCK))
        elif args.command == "join":
            join(args.manifest, args.output)
        else:
            json.dump(summary(args.bundle), sys.stdout, indent=2)
            sys.stdout.write("\n")
        return 0
    except (OSError, EOFError, ValueError, RuntimeError, KeyError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
