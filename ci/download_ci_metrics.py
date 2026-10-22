#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["ijson>=3.3,<4"]
# ///
"""Download, transport, and stream CI metrics. See ci/metrics-analysis.md.

Run with uv; only fetch needs an authenticated GitHub CLI. The bundle keeps
the original artifact documents, including the full planning snapshots.
"""

import argparse
from collections import Counter
import datetime as dt
import gzip
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import urlencode
import zipfile

BLOCK = 1024 * 1024
RUN_FIELDS = ("id", "html_url", "head_sha", "head_branch", "event", "created_at",
              "status", "conclusion", "run_attempt")


def api(endpoint, output=None):
    """Use gh's existing authentication; never copy credentials into a bundle."""
    result = subprocess.run(
        ["gh", "api", "--hostname", "github.com", "--method", "GET", endpoint],
        stdout=output if output is not None else subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        error = result.stderr.decode(errors="replace").strip()
        # Redirect errors can include a storage URL carrying a signed token.
        error = re.sub(r'(https?://[^\s?"\\]+)\?[^\s"\\]+', r'\1?[redacted]', error)
        raise RuntimeError(error)
    return result.stdout


def pages(endpoint, key):
    page = 1
    while True:
        separator = "&" if "?" in endpoint else "?"
        data = json.loads(api(f"{endpoint}{separator}per_page=100&page={page}"))
        if key == "workflow_runs" and data["total_count"] > 1000:
            raise RuntimeError("GitHub limits filtered run searches to 1000 results; use a smaller time window.")
        yield from data[key]
        if len(data[key]) < 100:
            return
        page += 1


def stamp(value):
    return value.astimezone(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def timestamp(value):
    try:
        result = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
        if result.tzinfo is None:
            raise ValueError("include a timezone, for example 2026-10-21T12:00:00Z")
        return result.astimezone(dt.timezone.utc)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def positive(value):
    result = float(value)
    if not math.isfinite(result) or result <= 0:
        raise argparse.ArgumentTypeError("must be a positive finite number")
    return result


def artifact_documents(base, artifact_id):
    # Spool the ZIP to disk; do not retain both the compressed and expanded
    # history in memory. Only one artifact's decoded documents are held at once.
    with tempfile.TemporaryFile() as packed:
        api(f"{base}/artifacts/{artifact_id}/zip", packed)
        packed.seek(0)
        with zipfile.ZipFile(packed) as archive:
            names = [n for n in archive.namelist() if n.endswith(".json") and not n.endswith("/")]
            if not names:
                raise ValueError("Artifact contains no JSON files")
            return {name: json.loads(archive.read(name)) for name in names}


def fetch(args):
    end = args.end or dt.datetime.now(dt.timezone.utc).replace(microsecond=0)
    start = args.start or end - dt.timedelta(hours=args.hours or 8)
    if start >= end:
        raise ValueError("start must precede end")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", args.repository):
        raise ValueError("repository must be owner/repo")
    output = args.output
    if output.suffix != ".gz":
        raise ValueError("output must end in .gz (the bundle is gzip-compressed JSON)")
    output.parent.mkdir(parents=True, exist_ok=True)
    base = f"repos/{args.repository}/actions"
    query = urlencode({"created": f"{stamp(start)}..{stamp(end)}"})
    header = {"schema_version": 1, "repository": args.repository, "workflow": args.workflow,
              "start": stamp(start), "end": stamp(end), "window_basis": "workflow run created_at",
              "downloaded_at": stamp(dt.datetime.now(dt.timezone.utc))}
    missing, errors = [], []
    saved = inspected = 0
    # Exclusive creation refuses overwrites before any API calls. Fatal errors
    # remove the incomplete stream; per-run failures produce a readable bundle.
    raw = output.open("xb")
    try:
        with raw:
            with gzip.open(raw, "wt", encoding="utf-8", compresslevel=6) as stream:
                stream.write(json.dumps(header)[:-1] + ',"runs":[')
                for run in pages(f"{base}/workflows/{args.workflow}/runs?{query}", "workflow_runs"):
                    inspected += 1
                    meta = {k: run.get(k) for k in RUN_FIELDS}
                    print(f"Run {run['id']} ({run['status']})", file=sys.stderr)
                    try:
                        artifacts = [a for a in pages(f"{base}/runs/{run['id']}/artifacts", "artifacts")
                                     if a["name"] == "ci-metrics"]
                    except (RuntimeError, ValueError, OSError) as error:
                        errors.append({"run": meta, "error": str(error)})
                        continue
                    if not artifacts:
                        missing.append({"run": meta, "reason": "No ci-metrics artifact"})
                    for artifact in sorted(artifacts, key=lambda a: a["id"]):
                        try:
                            if artifact.get("expired"):
                                raise ValueError("Artifact expired")
                            documents = artifact_documents(base, artifact["id"])
                        except (RuntimeError, ValueError, OSError, zipfile.BadZipFile) as error:
                            errors.append({"run": meta, "artifact_id": artifact["id"], "error": str(error)})
                            continue
                        if saved:
                            stream.write(",")
                        json.dump({"run": meta, "artifact_id": artifact["id"],
                                   "artifact": {k: artifact.get(k) for k in
                                                ("id", "name", "created_at", "updated_at", "size_in_bytes")},
                                   "files": documents}, stream, separators=(",", ":"))
                        saved += 1
                        del documents
                stream.write('],"inspected_runs":' + str(inspected) + ',"missing":')
                json.dump(missing, stream, separators=(",", ":"))
                stream.write(',"errors":')
                json.dump(errors, stream, separators=(",", ":"))
                stream.write("}\n")
    except BaseException:
        output.unlink(missing_ok=True)
        raise
    print(f"Saved {saved} artifacts from {inspected} runs to {output}; "
          f"{len(missing)} missing; {len(errors)} errors.", file=sys.stderr)
    return 1 if errors else 0


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
                           "window_basis", "downloaded_at", "inspected_runs"):
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
    download = commands.add_parser("fetch", help="download a time window as compact gzip JSON")
    download.add_argument("--repository", default="pyca/verified-garbage")
    download.add_argument("--workflow", default="ci.yml")
    window = download.add_mutually_exclusive_group()
    window.add_argument("--hours", type=positive, help="look back from --end (default: 8)")
    window.add_argument("--start", type=timestamp, help="inclusive ISO timestamp with timezone")
    download.add_argument("--end", type=timestamp, help="inclusive ISO timestamp (default: now)")
    download.add_argument("--output", type=Path, default=Path(".ci-metrics/ci-metrics.json.gz"))
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
        if args.command == "fetch":
            if not shutil.which("gh"):
                raise RuntimeError("Install GitHub CLI and authenticate with gh auth login first")
            return fetch(args)
        if args.command == "split":
            split(args.source, args.directory, int(args.part_mib * BLOCK))
        elif args.command == "join":
            join(args.manifest, args.output)
        else:
            json.dump(summary(args.bundle), sys.stdout, indent=2)
            sys.stdout.write("\n")
        return 0
    except (OSError, EOFError, ValueError, RuntimeError, KeyError, zipfile.BadZipFile) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
