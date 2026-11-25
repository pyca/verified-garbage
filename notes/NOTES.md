Working files of pyca/verified-garbage#6494, as they were used, for review (not to be merged).
Paths in them are those of the session (`/tmp/sp`).

* `numeric_check.py P256Square.lean`: 20,000 random and edge inputs (first run inline, on the first draft).
* `sq.s`: the first draft of the square, sparse correction. `sq.py`: its and the product's llvm-mca cycles (it reads `double.raw`, `Dump.lean`'s output, so now gives the final draft).
* `var.py`: variants of `sq.s`: the early `extr`, `lsr`/`lsl`/`orr` for `extr`, all 720 product orders. Output on sq.s, instructions and cycles on neoverse-n2, -v2, -v1, apple-m1:
  base 93 [41, 41, 41, 53]; early extr 93 [42, 40, 42, 53]; then f orr 95 [41, 39, 41, 55]; f and e23 orr 97 [40, 38, 40, 56]; e23 orr 95 [41, 39, 41, 54]; best order (01 02 03 12 13 23) 93 [41, 39, 41, 51], next 42.
* `alloc.py`: scheduler and allocator; run alone, it printed the first listings, at llvm-mca's default dispatch width. `search.py`: the random search, at -dispatch=5 (run with 40 tries per worker, then 700). `put.py`: wrote the listings. `p256_aarch64_schedule.py` joins these three; run it as `ci/p256_aarch64_schedule.py` in a checkout of the PR (it finds the root from its own path).
* `bottleneck.py`: the resource analysis of the first `double`.
