// The functions of `src/ecdsa_p192_sha256.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_sha256_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
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
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -19246
	ori %r12, %r12, 10289
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 5227
	ori %r12, %r12, 51633
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, -26146
	ori %r12, %r12, 63542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	li %r8, 0
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 145
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 96
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
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
	li %r8, 1
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2333(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 81
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 145
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 96
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
20:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 96
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p192_sign}
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
	li %r8, 0
	stb %r8, 2288(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 33
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 97
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_init_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	bl {vg_sha256_update_scratch}
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	li %r5, 96
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	bl {vg_hmac_sha256_finalize_scratch}
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
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
