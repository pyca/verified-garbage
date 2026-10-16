Measurement only (never merge): RSA-2048 sign, verified-garbage's ADX path against aws-lc, on one CPU.

    cd bench-gap
    export OPENSSL_ia32cap=":~0x200000" VG_CPU_FEATURES=avx,avx2,bmi2,adx   # no IFMA for either
    cargo build --release
    taskset -c 2 target/release/gap ab 1500    # interleaved whole signs: medians and vg/aws ratio
    taskset -c 2 target/release/gap crt 400    # best TSC ticks: vg sign, checked, bare CRT; aws sign, modexp p + q
    taskset -c 2 target/release/gap mb         # best TSC ticks per call: aws bn_mul_mont sqr/mul, vg strict/lazy sqr/mul, aws 1024-bit modexp

The key is generated on first run and kept in key2048.pem.
