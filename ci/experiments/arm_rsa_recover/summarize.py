#!/usr/bin/env python3
"""Summarize one recorded prototype run; never imply full API speedups."""
import csv
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
metadata = json.loads((root / 'metadata.json').read_text())
print('Unproven recovery-core experiment; excludes setup and final factor extraction.\n')
print(f"Revision: `{metadata['revision']}`; execution: `{metadata['runner']}`.\n")
print('| Kernel | Modulus bits | Candidate | Separate / fused |')
print('|---|---:|---:|---:|')
for kernel in ['baseline', 'umaal']:
    with (root / f'{kernel}.csv').open() as f:
        for row in csv.DictReader(f):
            if int(row['case']) % 8 < 4:
                print(f"| {kernel} | {row['bits']} | {row['base']} | {float(row['speedup']):.2f}× |")
