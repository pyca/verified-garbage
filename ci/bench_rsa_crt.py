"""Measure RSA CRT loading with fixed Wycheproof keys and matched x86 features.

Build against OpenSSL 4 first (OPENSSL_DIR=... OPENSSL_STATIC=1 cargo bench
--manifest-path bench/Cargo.toml --no-run), then pass the primitives executable.
Each invocation writes raw Criterion output, estimates and reproduction metadata.
"""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess


# OpenSSL 4's five logical vectors, from doc/man3/OPENSSL_ia32cap.pod.
# Retain architectural SSE/SSE2/FXSR in LV0; all other extensions are explicit.
CONFIGS = {
    "baseline": ("none", "0x7000000:0:0:0:0"),
    "adx": ("bmi2,adx", "0x7000000:0x80100:0:0:0"),
    "ifma": (
        "avx,bmi2,adx,avx512f,avx512ifma,avx512vl",
        "0x1800000007000000:0x80290100:0:0:0",
    ),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--filter", default="^rsa_(from_crt|check_key)/")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    binary = args.binary.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    keys = output / "keys"
    keys.mkdir()
    for bits in (2048, 3072, 4096):
        source = root / f"wycheproof/testvectors_v1/rsa_pkcs1_{bits}_test.json"
        group = json.loads(source.read_text())["testGroups"][0]
        (keys / f"{bits}.pem").write_text(group["privateKeyPem"])
    metadata = {
        "revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip(),
        "diff": subprocess.check_output(["git", "diff"], cwd=root, text=True),
        "platform": platform.platform(),
        "cpuinfo": Path("/proc/cpuinfo").read_text(),
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "configs": CONFIGS,
        "rounds": args.rounds,
        "filter": args.filter,
        "keys_sha256": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in keys.iterdir()
        },
    }
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    rows = []
    for round_index in range(args.rounds):
        configs = list(CONFIGS.items())
        if round_index % 2:
            configs.reverse()
        for name, (features, caps) in configs:
            run_dir = output / f"{round_index}-{name}"
            run_dir.mkdir()
            env = dict(os.environ, VG_CPU_FEATURES=features, OPENSSL_ia32cap=caps,
                       VG_BENCHES="rsa", VG_RSA_BENCH_KEYS=str(keys))
            command = [str(binary), "--bench", args.filter, "--sample-size", "30",
                       "--warm-up-time", "0.3", "--measurement-time", "1"]
            print(f"round {round_index + 1}: {name}", flush=True)
            with (run_dir / "raw.log").open("w") as log:
                subprocess.run(command, cwd=run_dir, env=env, stdout=log,
                               stderr=subprocess.STDOUT, check=True)
            for estimate in sorted((run_dir / "target/criterion").glob("**/new/estimates.json")):
                relative = estimate.relative_to(run_dir / "target/criterion")
                group, library, size = relative.parts[:3]
                if library == "verified-garbage" and size.endswith("-unchecked"):
                    library = "verified-garbage-unchecked"
                    size = size.removesuffix("-unchecked")
                stats = json.loads(estimate.read_text())["mean"]
                rows.append([round_index + 1, name, group, library, size,
                             stats["point_estimate"],
                             stats["confidence_interval"]["lower_bound"],
                             stats["confidence_interval"]["upper_bound"]])
            # Retain estimates and raw samples, discard Criterion's duplicate history.
            shutil.rmtree(run_dir / "target/criterion/report", ignore_errors=True)
            with (output / "times.csv").open("w") as f:
                writer = csv.writer(f)
                writer.writerow(["round", "config", "group", "library", "bytes",
                                 "mean_ns", "ci95_low_ns", "ci95_high_ns"])
                writer.writerows(rows)


if __name__ == "__main__":
    main()
