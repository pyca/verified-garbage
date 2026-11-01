// The functions of `src/ecdsa_brainpoolp512r1_sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sha512_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -320(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 60
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -25431
	ori %r12, %r12, 105
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 56
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, -19065
	ori %r12, %r12, 38530
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 52
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, 2141
	ori %r12, %r12, 56029
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 48
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, 7601
	ori %r12, %r12, 54145
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 44
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, 32684
	ori %r12, %r12, 4167
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 40
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, 16774
	ori %r12, %r12, 24857
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 36
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, 19625
	ori %r12, %r12, 9753
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 32
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, 21822
	ori %r12, %r12, 23617
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 128(%r11)
	lis %r12, 28723
	ori %r12, %r12, 2160
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 64(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 132(%r11)
	lis %r12, -10653
	ori %r12, %r12, 40138
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 68(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 136(%r11)
	lis %r12, -19511
	ori %r12, %r12, 53774
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 72(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 140(%r11)
	lis %r12, -13520
	ori %r12, %r12, 36275
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 76(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 144(%r11)
	lis %r12, 13257
	ori %r12, %r12, 64519
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 80(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 148(%r11)
	lis %r12, 16340
	ori %r12, %r12, 59054
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 84(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 152(%r11)
	lis %r12, -9239
	ori %r12, %r12, 50315
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 88(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 156(%r11)
	lis %r12, -21795
	ori %r12, %r12, 40376
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 92(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 316
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 312
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 308
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 304
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 300
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 296
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 292
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 288
	stwbrx %r7, %r11, %r12
	lwz %r7, 128(%r11)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 284
	stwbrx %r7, %r11, %r12
	lwz %r7, 132(%r11)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 280
	stwbrx %r7, %r11, %r12
	lwz %r7, 136(%r11)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 276
	stwbrx %r7, %r11, %r12
	lwz %r7, 140(%r11)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 272
	stwbrx %r7, %r11, %r12
	lwz %r7, 144(%r11)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 268
	stwbrx %r7, %r11, %r12
	lwz %r7, 148(%r11)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 264
	stwbrx %r7, %r11, %r12
	lwz %r7, 152(%r11)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 260
	stwbrx %r7, %r11, %r12
	lwz %r7, 156(%r11)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 256
	stwbrx %r7, %r11, %r12
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
	lwz %r8, 256(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2397(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2401(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2405(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2409(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2413(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2417(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2421(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2425(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2429(%r9)
	lwz %r8, 304(%r11)
	stw %r8, 2433(%r9)
	lwz %r8, 308(%r11)
	stw %r8, 2437(%r9)
	lwz %r8, 312(%r11)
	stw %r8, 2441(%r9)
	lwz %r8, 316(%r11)
	stw %r8, 2445(%r9)
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
	li %r6, 193
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 321
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
	lwz %r8, 256(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2397(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2401(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2405(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2409(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2413(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2417(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2421(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2425(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2429(%r9)
	lwz %r8, 304(%r11)
	stw %r8, 2433(%r9)
	lwz %r8, 308(%r11)
	stw %r8, 2437(%r9)
	lwz %r8, 312(%r11)
	stw %r8, 2441(%r9)
	lwz %r8, 316(%r11)
	stw %r8, 2445(%r9)
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
	li %r6, 193
	addi %r7, %r12, 384
	bl {vg_sha512_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 321
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
	li %r9, 128
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
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_brainpoolp512r1_sign}
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
	addi %r1, %r1, 320
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
