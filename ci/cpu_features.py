#!/usr/bin/env python3
"""Choose native execution only when it preserves an SDE configuration's features.

The Rust probe is run once on the host and once under the shard's SDE model.
Intersect the model with VG_CPU_FEATURES, then require every resulting feature
on the host. Explicitly mask native runs so a newer host cannot select a backend
the emulated CPU would not select. An empty result must be `none`, not an empty
environment variable (which means unrestricted).
"""

import sys


def select(host: str, model: str, allowed: str) -> tuple[str, str]:
    available = set(filter(None, host.split(",")))
    required = set(filter(None, model.split(",")))
    if allowed == "none":
        required.clear()
    elif allowed:
        required.intersection_update(allowed.split(","))
    mode = "native" if required <= available else "sde"
    return mode, ",".join(sorted(required)) or "none"


if __name__ == "__main__":
    print("|".join(select(*sys.argv[1:])))
