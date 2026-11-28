"""Benchmarks this checkout against OpenSSL and aws-lc-rs, for numbers to
publish: every run, their results and the report, in one command.

    python3 ci/bench_publish.py OUT [--cpu N] BENCH[=FILTER] ... [rustls]

    python3 ci/bench_publish.py results --cpu 4 mlkem768 mlkem1024 mldsa44 mldsa65 mldsa87 \\
        x25519 ecdh_p256 ecdh_p384 ecdh_p521 \\
        'ecdsa_p256=^ecdsa_p256_sha256_(sign|verify)/[^/]+/64$' \\
        'ecdsa_p384=^ecdsa_p384_sha384_(sign|verify)/[^/]+/64$' \\
        'ecdsa_p521=^ecdsa_p521_sha512_(sign|verify)/[^/]+/64$' \\
        rsa_pkcs1_sig 'rsa_pss=^rsa_pss_sha(256|384|512)_mgf1_sha(256|384|512)_(sign|verify)/' \\
        sha256 hmac_sha256 chacha20poly1305 aes_gcm rustls

Each BENCH is a benchmark of bench/benches/primitives (a file's name, a
`BENCHES` entry of its main.rs), with, after `=`, a regular expression over
its benchmark ids (`<group>/<library>/<size>`) for Criterion; `rustls` is
the rustls provider's suite (crates/rustls-verified-garbage/bench/run.sh,
Linux only), against aws-lc-rs.

Unlike `ci/bench_compare.py`, which looks for a slowdown of this library,
every library is measured alike. The benchmark binary is copied to
`--copies` new files, one after the other (which physical pages a file's
code and tables are read into moves some benchmarks by several percent, for
every library: see bench_compare.py), and each copy runs every benchmark
selected, of every library, with Criterion's default 100 samples after
`--warm-up-time` and over `--measurement-time`. A benchmark's time is the
median, over the copies, of Criterion's median estimate.

What is measured:

* This checkout, with every CPU feature it detects.
* The OpenSSL that the `openssl` crate finds: `OPENSSL_DIR`'s (linked
  statically with `OPENSSL_STATIC=1`), which is built beforehand, or the
  system's (before OpenSSL 3.5, with `--features ''`).
* The aws-lc-rs (and aws-lc-sys, so AWS-LC) of bench/Cargo.lock. The
  rustls checkout's is set to the same versions.

Run it on a machine doing nothing else, with `--cpu` (Linux), and check
`run.log`'s load averages. It needs cargo, a C compiler and cmake. In OUT:

    primitives.json, rustls.json   results files (ci/bench_report.py's format)
    primitives.csv                 every copy's time of each benchmark, and
                                   their spread, (max - min) / median
    report.html                    their charts
    environment.txt                the machine, and every version measured
    run.log                        each run's time and the load average
    raw/                           each copy's Criterion directory and
                                   output; rustls-bench's rows
"""

import argparse
import contextlib
import csv
import io
import json
import os
import pathlib
import platform
import re
import shutil
import statistics
import subprocess
import sys
import time
import tomllib

import bench_report
from bench_compare import cpu_model

ROOT = pathlib.Path(__file__).resolve().parent.parent
RUSTLS = ROOT / "crates/rustls-verified-garbage"
SIZES = "16|64|256|1024|16384"
# The charts the report starts with (`bench_report.py html --chart`); the
# rest of what was measured is in the page.
CHARTS = [
    "mlkem768_(keygen|encaps|decaps) mlkem1024_(keygen|encaps|decaps)",
    "mldsa(44|65|87)_(keygen|sign|verify)",
    "x25519 ecdh_p(256|384|521)",
    "ecdsa_p(256_sha256|384_sha384|521_sha512)_sign ecdsa_p(256_sha256|384_sha384|521_sha512)_verify",
    "rsa_pkcs1_sign rsa_pkcs1_verify",
    "rsa_pss_sha256_mgf1_sha256_sign rsa_pss_sha256_mgf1_sha256_verify",
    "aes-128-gcm-encrypt aes-128-gcm-decrypt",
    "aes-128-gcm-tls-seal aes-128-gcm-tls-open",
    "aes-256-gcm-tls-seal aes-256-gcm-tls-open",
    f"chacha20poly1305-encrypt/({SIZES}) chacha20poly1305-decrypt/({SIZES})",
    "sha256/(32|64|128|256|1024|16384)",
    "hmac-sha256",
    r"rustls-tls-1\.3-handshake-(client|server)",
    r"rustls-tls-1\.3-bulk-(send|recv)",
]


def sh(*cmd, cwd=None, env=None, out=None):
    """Runs `cmd`, which must succeed, returning its output (or, with `out`,
    writing its output and errors there)."""
    print("+", *cmd, file=sys.stderr)
    cmd = [str(c) for c in cmd]
    if out is None:
        return subprocess.run(cmd, cwd=cwd, env=env, check=True, stdout=subprocess.PIPE, text=True).stdout
    with open(out, "a") as f:
        subprocess.run(cmd, cwd=cwd, env=env, check=True, stdout=f, stderr=subprocess.STDOUT)


def locked(lock, name):
    """The version of the crate `name` in the Cargo.lock at `lock`: the one
    version, since two would be two libraries under one name."""
    versions = [p["version"] for p in tomllib.loads(lock.read_text())["package"] if p["name"] == name]
    if len(versions) != 1:
        raise SystemExit(f"{lock}: {name} is locked at {versions or 'no version'}, not at one")
    return versions[0]


def primitives(binary, benches, args, raw, log):
    """Runs `benches` (name to Criterion filter) from each copy of `binary`,
    returning each benchmark's times, one per copy."""
    pin = ["taskset", "-c", args.cpu] if args.cpu is not None else []
    times = {}
    for n in range(args.copies):
        d = raw / f"copy-{n + 1}"
        d.mkdir(parents=True)
        # A new file: the page cache holds a file's pages by inode, so this
        # copy's code and tables are read into newly chosen physical pages.
        copy = d / "primitives"
        shutil.copyfile(binary, copy)
        copy.chmod(0o755)
        for name, pattern in benches.items():
            log(f"copy {n + 1}/{args.copies}: {name}")
            sh(*pin, copy, "--bench", "--warm-up-time", args.warm_up_time, "--measurement-time",
               args.measurement_time, *([pattern] if pattern else []), out=d / f"{name}.out",
               env={**os.environ, "VG_BENCHES": name, "CRITERION_HOME": str(d / "criterion")})
        copy.unlink()
        for group, library, size, t in bench_report.read_criterion(d / "criterion"):
            times.setdefault((group, library, size), []).append(t)
    log("primitives: done")
    short = [key for key, ts in times.items() if len(ts) != args.copies]
    if short or not times:
        raise SystemExit(f"not measured in every copy: {short or 'anything'}")
    return dict(sorted(times.items(), key=lambda kv: (bench_report.natural(kv[0][0]),
                                                      bench_report.natural(str(kv[0][2])), kv[0][1])))


def rustls(args, out, lock, env, log):
    """Runs the rustls provider's benchmarks, with the aws-lc-rs of `lock`,
    returning the results file."""
    checkout = ROOT / "target/rustls"
    if not checkout.is_dir():
        sh(RUSTLS / "rustls/setup.sh", checkout)
    sh("cargo", "update", "-p", "aws-lc-rs", "--precise", locked(lock, "aws-lc-rs"), cwd=checkout)
    sh("cargo", "update", "-p", "aws-lc-sys", "--precise", locked(lock, "aws-lc-sys"), cwd=checkout)
    log("rustls")
    sh(RUSTLS / "bench/run.sh", args.rustls_rounds, out=out / "raw/rustls.out",
       env={**env, "BENCH_OUT": str(out / "raw/rustls"), **({"BENCH_CPU": args.cpu} if args.cpu is not None else {})})
    log("rustls: done")
    # Again, to name what aws-lc-rs was measured.
    sh(sys.executable, RUSTLS / "bench/results.py", out / "raw/rustls",
       "--meta", f"aws_lc=aws-lc-rs {locked(lock, 'aws-lc-rs')} (aws-lc-sys {locked(lock, 'aws-lc-sys')})")
    return out / "raw/rustls/rustls-bench.json"


def view(files):
    """`files` (results files) with the groups a chart needs side by side
    named for it, and no time changed: one-shot ChaCha20-Poly1305 encryption
    as `-encrypt`, beside `-decrypt`; and beside rustls-bench's scenarios,
    its full TLS 1.3 handshakes with server authentication only
    (TLS13_AES_128_GCM_SHA256) by side, each certificate type a "size", and
    its TLS 1.3 bulk transfers in records of the default size (16 KiB) by
    direction, each SHA-256 suite's AEAD a "size"."""
    handshake = re.compile(r"rustls-handshakes-TLSv1_3-(\w+)-TLS13_AES_128_GCM_SHA256-(client|server)-server-auth")
    bulk = re.compile(r"rustls-bulk-TLSv1_3-TLS13_(\w+)_SHA256-(send|recv)")
    for f in files:
        for r in list(f["results"]):
            if r["group"] == "chacha20poly1305":
                r["group"] = "chacha20poly1305-encrypt"
            elif (m := handshake.fullmatch(r["group"])) and r["size"] == "no-resume":
                f["results"].append({**r, "group": f"rustls-tls-1.3-handshake-{m[2]}", "size": m[1]})
            elif (m := bulk.fullmatch(r["group"])) and r["size"] == "default":
                f["results"].append({**r, "group": f"rustls-tls-1.3-bulk-{m[2]}", "size": m[1].replace("_", "-")})
    return files


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("out", type=pathlib.Path, help="a new directory for everything the run writes")
    p.add_argument("benches", nargs="+", metavar="BENCH[=FILTER]", help="benchmarks to run, or `rustls`")
    p.add_argument("--cpu", help="pin every run to this CPU (Linux)")
    p.add_argument("--copies", type=int, default=5)
    p.add_argument("--warm-up-time", default="1")
    p.add_argument("--measurement-time", default="2")
    p.add_argument("--rustls-rounds", default="5")
    p.add_argument("--features", default="openssl-argon2,openssl-gcm-siv,openssl-mldsa,openssl-mlkem",
                   help="the benchmark crate's features, comma-separated")
    args = p.parse_args(argv)
    out = args.out.resolve()
    if (out / "raw").exists():
        p.error(f"{out} has a run's results already")
    benches = dict(b.partition("=")[::2] for b in args.benches)
    with_rustls = benches.pop("rustls", None) is not None
    (out / "raw").mkdir(parents=True)

    def log(what):
        load = os.getloadavg() if hasattr(os, "getloadavg") else ()
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {what} load={' '.join(f'{x:.2f}' for x in load)}"
        print(line, file=sys.stderr)
        with open(out / "run.log", "a") as f:
            f.write(line + "\n")

    # The `openssl` command of the OpenSSL that is linked, for its version.
    env, tool = dict(os.environ), "openssl"
    if prefix := os.environ.get("OPENSSL_DIR"):
        tool = pathlib.Path(prefix) / "bin/openssl"
        env["LD_LIBRARY_PATH"] = f"{prefix}/lib:{prefix}/lib64"
    lock = ROOT / "bench/Cargo.lock"
    aws_lc = f"aws-lc-rs {locked(lock, 'aws-lc-rs')} (aws-lc-sys {locked(lock, 'aws-lc-sys')})"
    openssl_version = sh(tool, "version", env=env).strip()
    context = {
        "arch": bench_report.arch_name(),
        "os": platform.system(),
        "cpu": cpu_model(),
        "cpu_features": "",
        "ref": bench_report.git(ROOT, "rev-parse", "--abbrev-ref", "HEAD"),
        "date": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "local",
        "openssl": openssl_version,
        "aws_lc": aws_lc,
        "method": f"Criterion, {args.warm_up_time} s warm-up, {args.measurement_time} s measurement;"
                  f" median of {args.copies} fresh copies of the binary",
    }
    commit = bench_report.commit_of(ROOT)
    (out / "environment.txt").write_text("\n".join([
        f"verified-garbage: {commit} ({bench_report.git(ROOT, 'status', '--short') or 'clean'})",
        f"cpu: {context['cpu']}",
        f"platform: {platform.platform()}",
        f"aws-lc: {aws_lc}",
        f"rust: {sh('rustc', '-vV')}",
        f"cc: {sh('cc', '--version')}",
        f"openssl: {sh(tool, 'version', '-a', env=env)}",
    ]))
    shutil.copy(lock, out / "bench-Cargo.lock")

    files = []
    if benches:
        build = sh("cargo", "bench", "--no-run", "--message-format=json-render-diagnostics",
                   *(["--features", args.features] if args.features else []), cwd=ROOT / "bench", env=env)
        binary = next(m["executable"] for m in map(json.loads, build.splitlines())
                      if m.get("reason") == "compiler-artifact" and m.get("executable")
                      and m["target"]["name"] == "primitives")
        times = primitives(binary, benches, args, out / "raw", log)
        results = [bench_report.record(group, library, size, statistics.median(ts), samples=ts, commit=commit)
                   for (group, library, size), ts in times.items()]
        (out / "primitives.json").write_text(json.dumps(bench_report.document(context, results), indent=1) + "\n")
        files.append(out / "primitives.json")
        with open(out / "primitives.csv", "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["group", "library", "size", *(f"copy{i + 1}_ns" for i in range(args.copies)),
                        "median_ns", "spread"])
            for (group, library, size), ts in times.items():
                median = statistics.median(ts)
                w.writerow([group, library, size, *(f"{t:.3f}" for t in ts), f"{median:.3f}",
                            f"{(max(ts) - min(ts)) / median:.4f}"])
    if with_rustls:
        shutil.copy(rustls(args, out, lock, env, log), out / "rustls.json")
        shutil.copy(ROOT / "target/rustls/Cargo.lock", out / "rustls-Cargo.lock")
        files.append(out / "rustls.json")

    data = view(bench_report.load(files))
    title = f"verified-garbage, {openssl_version.split(' (')[0]} and {aws_lc}: {context['cpu']}"
    # (Without its warnings of the charts whose benchmarks did not run.)
    with contextlib.redirect_stderr(io.StringIO()):
        charts = bench_report.charts(CHARTS, data)
    page = bench_report.embed(bench_report.TEMPLATE.read_text(), data, title, charts)
    (out / "report.html").write_text(page)
    print(f"{out}/report.html", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
