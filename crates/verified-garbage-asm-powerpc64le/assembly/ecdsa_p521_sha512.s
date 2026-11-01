// The functions of `src/ecdsa_p521_sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sha512_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -400(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 256(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 260(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 264(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 268(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 28(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 32(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 36(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 40(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 44(%r9)
	stw %r8, 300(%r11)
	lwz %r8, 48(%r9)
	stw %r8, 304(%r11)
	lwz %r8, 52(%r9)
	stw %r8, 308(%r11)
	lwz %r8, 56(%r9)
	stw %r8, 312(%r11)
	lwz %r8, 60(%r9)
	stw %r8, 316(%r11)
	addi %r11, %r1, 0
	ld %r3, 216(%r11)
	addi %r7, %r1, 256
	li %r9, 58
	ldbrx %r8, %r7, %r9
	std %r8, 2560(%r3)
	li %r9, 50
	ldbrx %r8, %r7, %r9
	std %r8, 2568(%r3)
	li %r9, 42
	ldbrx %r8, %r7, %r9
	std %r8, 2576(%r3)
	li %r9, 34
	ldbrx %r8, %r7, %r9
	std %r8, 2584(%r3)
	li %r9, 26
	ldbrx %r8, %r7, %r9
	std %r8, 2592(%r3)
	li %r9, 18
	ldbrx %r8, %r7, %r9
	std %r8, 2600(%r3)
	li %r9, 10
	ldbrx %r8, %r7, %r9
	std %r8, 2608(%r3)
	li %r9, 2
	ldbrx %r8, %r7, %r9
	std %r8, 2616(%r3)
	li %r9, 0
	ldbrx %r8, %r7, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2624(%r3)
	ld %r4, 2560(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2568(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2560(%r3)
	ld %r4, 2568(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2576(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2568(%r3)
	ld %r4, 2576(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2584(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2576(%r3)
	ld %r4, 2584(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2592(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2584(%r3)
	ld %r4, 2592(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2600(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2592(%r3)
	ld %r4, 2600(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2608(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2600(%r3)
	ld %r4, 2608(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2616(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2608(%r3)
	ld %r4, 2616(%r3)
	rldicl %r4, %r4, 55, 9
	ld %r8, 2624(%r3)
	rldicr %r8, %r8, 55, 8
	or %r4, %r4, %r8
	std %r4, 2616(%r3)
	ld %r4, 2624(%r3)
	rldicl %r4, %r4, 55, 9
	std %r4, 2624(%r3)
	li %r10, 0
	addi %r10, %r10, -1
	ld %r4, 2560(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r7, %r6
	ld %r4, 2568(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r7, %r6
	ld %r4, 2576(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r7, %r6
	ld %r4, 2584(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r7, %r6
	ld %r4, 2592(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r7, %r6
	ld %r4, 2600(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r7, %r6
	ld %r4, 2608(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r7, %r6
	ld %r4, 2616(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r7, %r6
	ld %r4, 2624(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r7)
	stb %r4, 1(%r7)
	addi %r11, %r1, 0
	lis %r9, 257
	ori %r9, %r9, 257
	li %r10, 0
	stw %r9, 96(%r11)
	stw %r10, 32(%r11)
	stw %r9, 100(%r11)
	stw %r10, 36(%r11)
	stw %r9, 104(%r11)
	stw %r10, 40(%r11)
	stw %r9, 108(%r11)
	stw %r10, 44(%r11)
	stw %r9, 112(%r11)
	stw %r10, 48(%r11)
	stw %r9, 116(%r11)
	stw %r10, 52(%r11)
	stw %r9, 120(%r11)
	stw %r10, 56(%r11)
	stw %r9, 124(%r11)
	stw %r10, 60(%r11)
	stw %r9, 128(%r11)
	stw %r10, 64(%r11)
	stw %r9, 132(%r11)
	stw %r10, 68(%r11)
	stw %r9, 136(%r11)
	stw %r10, 72(%r11)
	stw %r9, 140(%r11)
	stw %r10, 76(%r11)
	stw %r9, 144(%r11)
	stw %r10, 80(%r11)
	stw %r9, 148(%r11)
	stw %r10, 84(%r11)
	stw %r9, 152(%r11)
	stw %r10, 88(%r11)
	stw %r9, 156(%r11)
	stw %r10, 92(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	ld %r7, 224(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2353(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2357(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2361(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2365(%r9)
	lwz %r8, 48(%r10)
	stw %r8, 2369(%r9)
	lwz %r8, 52(%r10)
	stw %r8, 2373(%r9)
	lwz %r8, 56(%r10)
	stw %r8, 2377(%r9)
	lwz %r8, 60(%r10)
	stw %r8, 2381(%r9)
	lbz %r8, 64(%r10)
	stb %r8, 2385(%r9)
	lbz %r8, 65(%r10)
	stb %r8, 2386(%r9)
	li %r8, 0
	stb %r8, 2387(%r9)
	stb %r8, 2388(%r9)
	lwz %r8, 0(%r7)
	stw %r8, 2389(%r9)
	lwz %r8, 4(%r7)
	stw %r8, 2393(%r9)
	lwz %r8, 8(%r7)
	stw %r8, 2397(%r9)
	lwz %r8, 12(%r7)
	stw %r8, 2401(%r9)
	lwz %r8, 16(%r7)
	stw %r8, 2405(%r9)
	lwz %r8, 20(%r7)
	stw %r8, 2409(%r9)
	lwz %r8, 24(%r7)
	stw %r8, 2413(%r9)
	lwz %r8, 28(%r7)
	stw %r8, 2417(%r9)
	lwz %r8, 32(%r7)
	stw %r8, 2421(%r9)
	lwz %r8, 36(%r7)
	stw %r8, 2425(%r9)
	lwz %r8, 40(%r7)
	stw %r8, 2429(%r9)
	lwz %r8, 44(%r7)
	stw %r8, 2433(%r9)
	lwz %r8, 48(%r7)
	stw %r8, 2437(%r9)
	lwz %r8, 52(%r7)
	stw %r8, 2441(%r9)
	lwz %r8, 56(%r7)
	stw %r8, 2445(%r9)
	lwz %r8, 60(%r7)
	stw %r8, 2449(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 197
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 325
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 192
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	ld %r7, 224(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 1
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2353(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2357(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2361(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2365(%r9)
	lwz %r8, 48(%r10)
	stw %r8, 2369(%r9)
	lwz %r8, 52(%r10)
	stw %r8, 2373(%r9)
	lwz %r8, 56(%r10)
	stw %r8, 2377(%r9)
	lwz %r8, 60(%r10)
	stw %r8, 2381(%r9)
	lbz %r8, 64(%r10)
	stb %r8, 2385(%r9)
	lbz %r8, 65(%r10)
	stb %r8, 2386(%r9)
	li %r8, 0
	stb %r8, 2387(%r9)
	stb %r8, 2388(%r9)
	lwz %r8, 0(%r7)
	stw %r8, 2389(%r9)
	lwz %r8, 4(%r7)
	stw %r8, 2393(%r9)
	lwz %r8, 8(%r7)
	stw %r8, 2397(%r9)
	lwz %r8, 12(%r7)
	stw %r8, 2401(%r9)
	lwz %r8, 16(%r7)
	stw %r8, 2405(%r9)
	lwz %r8, 20(%r7)
	stw %r8, 2409(%r9)
	lwz %r8, 24(%r7)
	stw %r8, 2413(%r9)
	lwz %r8, 28(%r7)
	stw %r8, 2417(%r9)
	lwz %r8, 32(%r7)
	stw %r8, 2421(%r9)
	lwz %r8, 36(%r7)
	stw %r8, 2425(%r9)
	lwz %r8, 40(%r7)
	stw %r8, 2429(%r9)
	lwz %r8, 44(%r7)
	stw %r8, 2433(%r9)
	lwz %r8, 48(%r7)
	stw %r8, 2437(%r9)
	lwz %r8, 52(%r7)
	stw %r8, 2441(%r9)
	lwz %r8, 56(%r7)
	stw %r8, 2445(%r9)
	lwz %r8, 60(%r7)
	stw %r8, 2449(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 197
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 325
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 192
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
20:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 192
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 328(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 332(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 336(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 340(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 344(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 348(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 352(%r11)
	lwz %r8, 124(%r11)
	stw %r8, 356(%r11)
	lwz %r8, 128(%r11)
	stw %r8, 360(%r11)
	lwz %r8, 132(%r11)
	stw %r8, 364(%r11)
	lwz %r8, 136(%r11)
	stw %r8, 368(%r11)
	lwz %r8, 140(%r11)
	stw %r8, 372(%r11)
	lwz %r8, 144(%r11)
	stw %r8, 376(%r11)
	lwz %r8, 148(%r11)
	stw %r8, 380(%r11)
	lwz %r8, 152(%r11)
	stw %r8, 384(%r11)
	lwz %r8, 156(%r11)
	stw %r8, 388(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 192
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	ld %r8, 96(%r11)
	std %r8, 392(%r11)
	addi %r11, %r1, 0
	ld %r3, 216(%r11)
	addi %r7, %r1, 328
	li %r9, 58
	ldbrx %r8, %r7, %r9
	std %r8, 2560(%r3)
	li %r9, 50
	ldbrx %r8, %r7, %r9
	std %r8, 2568(%r3)
	li %r9, 42
	ldbrx %r8, %r7, %r9
	std %r8, 2576(%r3)
	li %r9, 34
	ldbrx %r8, %r7, %r9
	std %r8, 2584(%r3)
	li %r9, 26
	ldbrx %r8, %r7, %r9
	std %r8, 2592(%r3)
	li %r9, 18
	ldbrx %r8, %r7, %r9
	std %r8, 2600(%r3)
	li %r9, 10
	ldbrx %r8, %r7, %r9
	std %r8, 2608(%r3)
	li %r9, 2
	ldbrx %r8, %r7, %r9
	std %r8, 2616(%r3)
	li %r9, 0
	ldbrx %r8, %r7, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2624(%r3)
	ld %r4, 2560(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2568(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2560(%r3)
	ld %r4, 2568(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2576(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2568(%r3)
	ld %r4, 2576(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2584(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2576(%r3)
	ld %r4, 2584(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2592(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2584(%r3)
	ld %r4, 2592(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2600(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2592(%r3)
	ld %r4, 2600(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2608(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2600(%r3)
	ld %r4, 2608(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2616(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2608(%r3)
	ld %r4, 2616(%r3)
	rldicl %r4, %r4, 57, 7
	ld %r8, 2624(%r3)
	rldicr %r8, %r8, 57, 6
	or %r4, %r4, %r8
	std %r4, 2616(%r3)
	ld %r4, 2624(%r3)
	rldicl %r4, %r4, 57, 7
	std %r4, 2624(%r3)
	li %r10, 0
	addi %r10, %r10, -1
	ld %r4, 2560(%r3)
	and %r4, %r4, %r10
	li %r6, 58
	stdbrx %r4, %r7, %r6
	ld %r4, 2568(%r3)
	and %r4, %r4, %r10
	li %r6, 50
	stdbrx %r4, %r7, %r6
	ld %r4, 2576(%r3)
	and %r4, %r4, %r10
	li %r6, 42
	stdbrx %r4, %r7, %r6
	ld %r4, 2584(%r3)
	and %r4, %r4, %r10
	li %r6, 34
	stdbrx %r4, %r7, %r6
	ld %r4, 2592(%r3)
	and %r4, %r4, %r10
	li %r6, 26
	stdbrx %r4, %r7, %r6
	ld %r4, 2600(%r3)
	and %r4, %r4, %r10
	li %r6, 18
	stdbrx %r4, %r7, %r6
	ld %r4, 2608(%r3)
	and %r4, %r4, %r10
	li %r6, 10
	stdbrx %r4, %r7, %r6
	ld %r4, 2616(%r3)
	and %r4, %r4, %r10
	li %r6, 2
	stdbrx %r4, %r7, %r6
	ld %r4, 2624(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 0(%r7)
	stb %r4, 1(%r7)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 328
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p521_sign}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 21f
	li %r12, 0
	b 22f
21:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 193
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 192
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha512_finalize_scratch}
	li %r12, 1
22:
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	addi %r11, %r1, 0
	li %r12, 0
	std %r12, 32(%r11)
	std %r12, 40(%r11)
	std %r12, 48(%r11)
	std %r12, 56(%r11)
	std %r12, 64(%r11)
	std %r12, 72(%r11)
	std %r12, 80(%r11)
	std %r12, 88(%r11)
	std %r12, 96(%r11)
	std %r12, 104(%r11)
	std %r12, 112(%r11)
	std %r12, 120(%r11)
	std %r12, 128(%r11)
	std %r12, 136(%r11)
	std %r12, 144(%r11)
	std %r12, 152(%r11)
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	std %r12, 256(%r11)
	std %r12, 264(%r11)
	std %r12, 272(%r11)
	std %r12, 280(%r11)
	std %r12, 288(%r11)
	std %r12, 296(%r11)
	std %r12, 304(%r11)
	std %r12, 312(%r11)
	std %r12, 320(%r11)
	std %r12, 328(%r11)
	std %r12, 336(%r11)
	std %r12, 344(%r11)
	std %r12, 352(%r11)
	std %r12, 360(%r11)
	std %r12, 368(%r11)
	std %r12, 376(%r11)
	std %r12, 384(%r11)
	std %r12, 392(%r11)
	addi %r1, %r1, 400
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
