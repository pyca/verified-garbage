Measurement only, not for merging: the generator of the hand-written
`vg_x25519` this branch measures (four 64-bit words, a multiplication by
rows, a square of its own, one carry chain and a masked fold in the
additions and subtractions, swaps of 64-bit words).

    python3 gen.py harness > new.S
    powerpc64le-linux-gnu-gcc -O1 -static -o h h.c new.S
    qemu-ppc64le-static ./h 40 | python3 check.py
