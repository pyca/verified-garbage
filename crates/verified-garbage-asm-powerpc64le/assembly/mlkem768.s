// The functions of `src/mlkem768.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen:
	mflr %r0
	std %r24, 840(%r6)
	std %r25, 848(%r6)
	std %r26, 856(%r6)
	std %r27, 864(%r6)
	std %r28, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	std %r31, 896(%r6)
	std %r0, 904(%r6)
	addi %r30, %r3, 0
	addi %r29, %r4, 0
	addi %r28, %r5, 0
	addi %r31, %r6, 0
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r30, 0
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 1184
	li %r7, 1
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	li %r6, 6
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 920
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 920
	addi %r4, %r31, 1248
	li %r5, 32
20:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	li %r26, 0
21:
	stb %r26, 984(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 952
	li %r7, 33
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1056
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1056
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
	bl {vg_mlkem_cbd2}
	rldicr %r3, %r26, 10, 53
	add %r3, %r31, %r3
	addi %r3, %r3, 5120
	addi %r4, %r31, 18432
	bl {vg_mlkem_ntt}
	addi %r26, %r26, 1
	addi %r0, %r26, -6
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	li %r24, 1
	li %r26, 0
22:
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
23:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	li %r25, 0
24:
	stb %r25, 1280(%r31)
	stb %r26, 1281(%r31)
	addi %r3, %r31, 1248
	addi %r4, %r31, 15360
	addi %r5, %r31, 16384
	bl {vg_mlkem_sample_ntt}
	and %r24, %r24, %r3
	cmpldi %cr0, %r3, 0
	beq %cr0, 25f
	addi %r4, %r31, 15360
	b 26f
25:
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
26:
	addi %r3, %r31, 14336
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	addi %r3, %r31, 13312
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 8192
	bl {vg_mlkem_add}
	addi %r3, %r31, 13312
	li %r0, 384
	mulld %r0, %r26, %r0
	add %r4, %r29, %r0
	bl {vg_mlkem_encode12}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	li %r26, 0
27:
	rldicr %r3, %r26, 10, 53
	add %r3, %r31, %r3
	addi %r3, %r3, 5120
	li %r0, 384
	mulld %r0, %r26, %r0
	add %r4, %r28, %r0
	bl {vg_mlkem_encode12}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 27b
	addi %r3, %r31, 1248
	addi %r4, %r29, 1152
	li %r5, 32
28:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	addi %r3, %r29, 0
	addi %r4, %r28, 1152
	li %r5, 1184
29:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r29, 0
	li %r7, 1184
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 6
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r28, 2336
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r30, 32
	addi %r4, %r28, 2368
	li %r5, 32
210:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r3, %r24, 0
	ld %r0, 904(%r31)
	mtlr %r0
	ld %r24, 840(%r31)
	ld %r25, 848(%r31)
	ld %r26, 856(%r31)
	ld %r27, 864(%r31)
	ld %r28, 872(%r31)
	ld %r29, 880(%r31)
	ld %r30, 888(%r31)
	ld %r31, 896(%r31)
	blr

vg_mlkem768_encaps:
	mflr %r0
	std %r24, 840(%r7)
	std %r25, 848(%r7)
	std %r26, 856(%r7)
	std %r27, 864(%r7)
	std %r28, 872(%r7)
	std %r29, 880(%r7)
	std %r30, 888(%r7)
	std %r31, 896(%r7)
	std %r0, 904(%r7)
	addi %r30, %r3, 0
	addi %r29, %r4, 0
	addi %r28, %r5, 0
	addi %r27, %r6, 0
	addi %r31, %r7, 0
	addi %r3, %r29, 0
	addi %r4, %r31, 1024
	li %r5, 32
20:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	addi %r29, %r31, 1024
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r30, 0
	li %r7, 1184
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 6
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 992
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 1024
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 992
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	li %r6, 6
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 920
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 920
	addi %r4, %r28, 0
	li %r5, 32
21:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 21b
	addi %r3, %r30, 1152
	addi %r4, %r31, 1248
	li %r5, 32
22:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	li %r26, 0
23:
	li %r0, 384
	mulld %r0, %r26, %r0
	add %r3, %r30, %r0
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	bl {vg_mlkem_decode12}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	li %r26, 0
24:
	stb %r26, 984(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 952
	li %r7, 33
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1056
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1056
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
	bl {vg_mlkem_cbd2}
	rldicr %r3, %r26, 10, 53
	add %r3, %r31, %r3
	addi %r3, %r3, 5120
	addi %r4, %r31, 18432
	bl {vg_mlkem_ntt}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	li %r26, 3
25:
	stb %r26, 984(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 952
	li %r7, 33
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1056
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1056
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
	bl {vg_mlkem_cbd2}
	addi %r26, %r26, 1
	addi %r0, %r26, -7
	cmpldi %cr0, %r0, 0
	bne %cr0, 25b
	addi %r3, %r29, 0
	li %r4, 32
	li %r5, 1
	addi %r6, %r31, 12288
	bl {vg_mlkem_decode_decompress}
	li %r24, 1
	li %r26, 0
26:
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
27:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	li %r25, 0
28:
	stb %r26, 1280(%r31)
	stb %r25, 1281(%r31)
	addi %r3, %r31, 1248
	addi %r4, %r31, 15360
	addi %r5, %r31, 16384
	bl {vg_mlkem_sample_ntt}
	and %r24, %r24, %r3
	cmpldi %cr0, %r3, 0
	beq %cr0, 29f
	addi %r4, %r31, 15360
	b 210f
29:
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
210:
	addi %r3, %r31, 14336
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 28b
	addi %r3, %r31, 13312
	addi %r4, %r31, 18432
	bl {vg_mlkem_inv_ntt}
	addi %r3, %r31, 13312
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 8192
	bl {vg_mlkem_add}
	li %r0, 320
	mulld %r0, %r26, %r0
	add %r5, %r27, %r0
	addi %r3, %r31, 13312
	li %r4, 10
	li %r6, 320
	bl {vg_mlkem_compress_encode}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 26b
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
211:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	li %r25, 0
212:
	addi %r3, %r31, 14336
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 212b
	addi %r3, %r31, 13312
	addi %r4, %r31, 18432
	bl {vg_mlkem_inv_ntt}
	addi %r3, %r31, 13312
	addi %r4, %r31, 11264
	bl {vg_mlkem_add}
	addi %r3, %r31, 13312
	addi %r4, %r31, 12288
	bl {vg_mlkem_add}
	addi %r3, %r31, 13312
	li %r4, 4
	addi %r5, %r27, 960
	li %r6, 128
	bl {vg_mlkem_compress_encode}
	addi %r3, %r24, 0
	ld %r0, 904(%r31)
	mtlr %r0
	ld %r24, 840(%r31)
	ld %r25, 848(%r31)
	ld %r26, 856(%r31)
	ld %r27, 864(%r31)
	ld %r28, 872(%r31)
	ld %r29, 880(%r31)
	ld %r30, 888(%r31)
	ld %r31, 896(%r31)
	blr

vg_mlkem768_decaps:
	mflr %r0
	std %r24, 840(%r6)
	std %r25, 848(%r6)
	std %r26, 856(%r6)
	std %r27, 864(%r6)
	std %r28, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	std %r31, 896(%r6)
	std %r0, 904(%r6)
	std %r5, 912(%r6)
	addi %r30, %r3, 0
	addi %r28, %r4, 0
	addi %r31, %r6, 0
	addi %r3, %r28, 0
	addi %r4, %r31, 24576
	li %r5, 1088
20:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	addi %r28, %r31, 24576
	li %r26, 0
21:
	li %r0, 320
	mulld %r0, %r26, %r0
	add %r3, %r28, %r0
	li %r4, 320
	li %r5, 10
	rldicr %r6, %r26, 10, 53
	add %r6, %r31, %r6
	addi %r6, %r6, 5120
	bl {vg_mlkem_decode_decompress}
	rldicr %r3, %r26, 10, 53
	add %r3, %r31, %r3
	addi %r3, %r3, 5120
	addi %r4, %r31, 18432
	bl {vg_mlkem_ntt}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	li %r26, 0
22:
	li %r0, 384
	mulld %r0, %r26, %r0
	add %r3, %r30, %r0
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	bl {vg_mlkem_decode12}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
23:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	li %r25, 0
24:
	addi %r3, %r31, 14336
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	addi %r3, %r31, 13312
	addi %r4, %r31, 18432
	bl {vg_mlkem_inv_ntt}
	addi %r3, %r28, 960
	li %r4, 128
	li %r5, 4
	addi %r6, %r31, 11264
	bl {vg_mlkem_decode_decompress}
	addi %r3, %r31, 11264
	addi %r4, %r31, 13312
	bl {vg_mlkem_sub}
	addi %r3, %r31, 11264
	li %r4, 1
	addi %r5, %r31, 1024
	li %r6, 32
	bl {vg_mlkem_compress_encode}
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 1024
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r30, 2336
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 72
	li %r6, 6
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 72
	addi %r6, %r31, 920
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r30, 2368
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 24576
	li %r7, 1088
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1216
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r30, %r30, 1152
	addi %r29, %r31, 1024
	addi %r27, %r31, 19456
	addi %r3, %r30, 1152
	addi %r4, %r31, 1248
	li %r5, 32
25:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	li %r26, 0
26:
	li %r0, 384
	mulld %r0, %r26, %r0
	add %r3, %r30, %r0
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	bl {vg_mlkem_decode12}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 26b
	li %r26, 0
27:
	stb %r26, 984(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 952
	li %r7, 33
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1056
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1056
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
	bl {vg_mlkem_cbd2}
	rldicr %r3, %r26, 10, 53
	add %r3, %r31, %r3
	addi %r3, %r3, 5120
	addi %r4, %r31, 18432
	bl {vg_mlkem_ntt}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 27b
	li %r26, 3
28:
	stb %r26, 984(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 952
	li %r7, 33
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1056
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1056
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
	bl {vg_mlkem_cbd2}
	addi %r26, %r26, 1
	addi %r0, %r26, -7
	cmpldi %cr0, %r0, 0
	bne %cr0, 28b
	addi %r3, %r29, 0
	li %r4, 32
	li %r5, 1
	addi %r6, %r31, 12288
	bl {vg_mlkem_decode_decompress}
	li %r24, 1
	li %r26, 0
29:
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
210:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	li %r25, 0
211:
	stb %r26, 1280(%r31)
	stb %r25, 1281(%r31)
	addi %r3, %r31, 1248
	addi %r4, %r31, 15360
	addi %r5, %r31, 16384
	bl {vg_mlkem_sample_ntt}
	and %r24, %r24, %r3
	cmpldi %cr0, %r3, 0
	beq %cr0, 212f
	addi %r4, %r31, 15360
	b 213f
212:
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 5120
213:
	addi %r3, %r31, 14336
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 211b
	addi %r3, %r31, 13312
	addi %r4, %r31, 18432
	bl {vg_mlkem_inv_ntt}
	addi %r3, %r31, 13312
	rldicr %r4, %r26, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 8192
	bl {vg_mlkem_add}
	li %r0, 320
	mulld %r0, %r26, %r0
	add %r5, %r27, %r0
	addi %r3, %r31, 13312
	li %r4, 10
	li %r6, 320
	bl {vg_mlkem_compress_encode}
	addi %r26, %r26, 1
	addi %r0, %r26, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 29b
	addi %r3, %r31, 13312
	li %r4, 0
	li %r5, 256
214:
	stw %r4, 0(%r3)
	addi %r3, %r3, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	li %r25, 0
215:
	addi %r3, %r31, 14336
	rldicr %r4, %r25, 10, 53
	add %r4, %r31, %r4
	addi %r4, %r4, 2048
	rldicr %r5, %r25, 10, 53
	add %r5, %r31, %r5
	addi %r5, %r5, 5120
	addi %r6, %r31, 18432
	bl {vg_mlkem_multiply_ntts}
	addi %r3, %r31, 13312
	addi %r4, %r31, 14336
	bl {vg_mlkem_add}
	addi %r25, %r25, 1
	addi %r0, %r25, -3
	cmpldi %cr0, %r0, 0
	bne %cr0, 215b
	addi %r3, %r31, 13312
	addi %r4, %r31, 18432
	bl {vg_mlkem_inv_ntt}
	addi %r3, %r31, 13312
	addi %r4, %r31, 11264
	bl {vg_mlkem_add}
	addi %r3, %r31, 13312
	addi %r4, %r31, 12288
	bl {vg_mlkem_add}
	addi %r3, %r31, 13312
	li %r4, 4
	addi %r5, %r27, 960
	li %r6, 128
	bl {vg_mlkem_compress_encode}
	addi %r3, %r28, 0
	addi %r4, %r31, 19456
	li %r12, 0
	li %r26, 1088
216:
	lbz %r5, 0(%r3)
	lbz %r6, 0(%r4)
	xor %r5, %r5, %r6
	or %r12, %r12, %r5
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 216b
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	li %r3, 0
	subf %r12, %r12, %r3
	addi %r3, %r31, 920
	addi %r4, %r31, 1216
	ld %r5, 912(%r31)
	li %r26, 32
217:
	lbz %r6, 0(%r3)
	lbz %r7, 0(%r4)
	xor %r6, %r6, %r7
	and %r6, %r6, %r12
	xor %r6, %r6, %r7
	stb %r6, 0(%r5)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 217b
	addi %r3, %r24, 0
	ld %r0, 904(%r31)
	mtlr %r0
	ld %r24, 840(%r31)
	ld %r25, 848(%r31)
	ld %r26, 856(%r31)
	ld %r27, 864(%r31)
	ld %r28, 872(%r31)
	ld %r29, 880(%r31)
	ld %r30, 888(%r31)
	ld %r31, 896(%r31)
	blr

vg_mlkem768_check_ek:
	li %r4, 384
	li %r5, 0
20:
	lbz %r6, 1(%r3)
	rldicr %r6, %r6, 60, 3
	rldicl %r6, %r6, 12, 52
	lbz %r7, 0(%r3)
	add %r6, %r6, %r7
	li %r7, 3328
	subf %r7, %r6, %r7
	rldicl %r7, %r7, 1, 63
	add %r5, %r5, %r7
	lbz %r6, 1(%r3)
	rldicl %r6, %r6, 60, 4
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 4, 59
	add %r6, %r6, %r7
	li %r7, 3328
	subf %r7, %r6, %r7
	rldicl %r7, %r7, 1, 63
	add %r5, %r5, %r7
	addi %r3, %r3, 3
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	li %r6, 0
	subf %r6, %r5, %r6
	rldicl %r6, %r6, 1, 63
	li %r3, 1
	subf %r3, %r6, %r3
	blr
