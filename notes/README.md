# Notes for the AArch64 Keccak-f[1600] clean-room work

The working scripts, as left when the design was done (committed together,
afterwards; their times were not recorded by commits).

* `frames.py`: the search for rotation frames that a round maps to itself.
* `gen.py`, `gen2.py`: generators of the general rounds; `explicit.py`: with explicit rotations.
* `sched.py`, `sched_s.py`, `orders.py`: list schedulers; `orders.py` prints the orders in `X2.lean` and `X3.lean`.
* `emit*.py`: prototypes for the Benchmarks workflow; `emu.py`: checks them in an emulator.

Measured by runs 45653155940, 45654055529, 45654665164, 45655287485 (prototypes), 45667860585 (end to end), 45670862366 (mixes again, emit6.py).
