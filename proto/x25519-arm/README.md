Measurement only, not for merging: the generator of the hand-written
`vg_x25519_umaal` this branch measures (eight 32-bit words, `umaal`).

    python3 gen.py > new.S
    arm-linux-gnueabihf-gcc -O1 -marm -march=armv7-a+fp -static -o h h.c new.S   # or -mthumb
    qemu-arm ./h 40 | python3 check.py
