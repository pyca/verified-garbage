#!/bin/sh
# check, write, assemble, commit, push: go.sh "<bodies>" "<message>"
set -e; cd "$(dirname "$0")"; python3 check.py; rm -rf __pycache__; cd ..; python3 lab/gen.py "$1"
python3 - <<'P'
import re
open('/tmp/lab.s','w').write(re.search(r'global_asm!\(r"(.*?)"\);',open('bench/benches/primitives/lab.rs').read(),re.S).group(1))
P
clang --target=aarch64-linux-gnu -c /tmp/lab.s -o /tmp/lab.o
git add -A; git commit -qm "$2"; git push -q
