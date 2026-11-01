// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 0
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	mflr %r0
	std %r0, 144(%r12)
	or %r28, %r3, %r3
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	or %r31, %r8, %r8
	li %r0, 0
	stb %r0, 168(%r12)
	li %r0, 2
	stb %r0, 169(%r12)
	ld %r4, 2320(%r12)
	addi %r11, %r12, 170
	li %r5, 0
	ld %r12, 2328(%r12)
20:
	lbz %r3, 0(%r4)
	stb %r3, 0(%r11)
	addi %r0, %r3, -1
	rldicl %r0, %r0, 1, 63
	or %r5, %r5, %r0
	addi %r4, %r4, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	li %r0, 0
	stb %r0, 0(%r11)
	addi %r11, %r11, 1
	addi %r12, %r1, 0
	cmpldi %cr0, %r10, 0
	bne %cr0, 21f
	b 22f
21:
	or %r7, %r9, %r9
	or %r4, %r11, %r11
	or %r8, %r10, %r10
23:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 23b
22:
	std %r5, 152(%r12)
	or %r3, %r28, %r28
	or %r4, %r29, %r29
	or %r7, %r30, %r30
	or %r8, %r31, %r31
	addi %r9, %r12, 168
	or %r10, %r29, %r29
	ld %r0, 2336(%r12)
	std %r0, 96(%r12)
	ld %r0, 2344(%r12)
	std %r0, 104(%r12)
	ld %r5, 2352(%r12)
	ld %r6, 2360(%r12)
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	ld %r9, 152(%r12)
	addi %r9, %r9, -1
	and %r3, %r3, %r9
	or %r11, %r28, %r28
	or %r8, %r29, %r29
24:
	lbz %r10, 0(%r11)
	and %r10, %r10, %r9
	stb %r10, 0(%r11)
	addi %r11, %r11, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 24b
	addi %r12, %r1, 0
	addi %r4, %r12, 168
	or %r11, %r29, %r29
	li %r0, 0
25:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	addi %r12, %r1, 0
	ld %r0, 144(%r12)
	mtlr %r0
	ld %r28, 112(%r12)
	ld %r29, 120(%r12)
	ld %r30, 128(%r12)
	ld %r31, 136(%r12)
	addi %r1, %r1, 2224
	blr

vg_rsa_pkcs1_decrypt:
	stdu %r1, -304(%r1)
	addi %r12, %r1, 0
	mflr %r0
	std %r0, 296(%r12)
	std %r3, 192(%r12)
	std %r5, 200(%r12)
	std %r6, 208(%r12)
	std %r7, 216(%r12)
	std %r8, 224(%r12)
	std %r9, 232(%r12)
	std %r10, 240(%r12)
	ld %r0, 400(%r12)
	std %r0, 248(%r12)
	ld %r0, 408(%r12)
	std %r0, 256(%r12)
	ld %r0, 504(%r12)
	std %r0, 264(%r12)
	ld %r0, 424(%r12)
	std %r0, 96(%r12)
	ld %r0, 432(%r12)
	std %r0, 104(%r12)
	ld %r0, 440(%r12)
	std %r0, 112(%r12)
	ld %r0, 448(%r12)
	std %r0, 120(%r12)
	ld %r0, 456(%r12)
	std %r0, 128(%r12)
	ld %r0, 464(%r12)
	std %r0, 136(%r12)
	ld %r0, 472(%r12)
	std %r0, 144(%r12)
	ld %r0, 480(%r12)
	std %r0, 152(%r12)
	ld %r0, 488(%r12)
	std %r0, 160(%r12)
	ld %r0, 496(%r12)
	std %r0, 168(%r12)
	ld %r0, 504(%r12)
	std %r0, 176(%r12)
	ld %r0, 512(%r12)
	std %r0, 184(%r12)
	or %r4, %r7, %r7
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	ld %r9, 256(%r12)
	or %r10, %r4, %r4
	bl {vg_rsa_private_checked}
	rlwinm %r3, %r3, 0, 0, 31
	addi %r12, %r1, 0
	std %r3, 272(%r12)
	ld %r11, 264(%r12)
	addi %r11, %r11, 2416
	ld %r9, 216(%r12)
	li %r0, 0
20:
	stb %r0, 0(%r11)
	addi %r11, %r11, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	ld %r10, 240(%r12)
	ld %r9, 248(%r12)
	ld %r11, 264(%r12)
	addi %r11, %r11, 2416
	ld %r8, 216(%r12)
	add %r11, %r11, %r8
	subf %r11, %r9, %r11
21:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 21b
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	bl {vg_sha256_init}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	li %r4, 0
	ld %r5, 264(%r12)
	addi %r5, %r5, 2416
	ld %r6, 216(%r12)
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 216(%r12)
	ld %r5, 264(%r12)
	addi %r5, %r5, 1040
	ld %r6, 264(%r12)
	addi %r6, %r6, 192
	bl {vg_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	ld %r5, 264(%r12)
	addi %r5, %r5, 1040
	li %r6, 32
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 256(%r12)
	ld %r6, 216(%r12)
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	ld %r5, 216(%r12)
	addi %r5, %r5, 64
	ld %r6, 264(%r12)
	addi %r6, %r6, 1104
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	li %r10, 0
	std %r10, 280(%r12)
	ld %r10, 216(%r12)
	addi %r10, %r10, 31
	rldicl %r10, %r10, 59, 5
	std %r10, 288(%r12)
22:
	addi %r12, %r1, 0
	ld %r9, 264(%r12)
	addi %r9, %r9, 1024
	ld %r11, 280(%r12)
	ld %r8, 216(%r12)
	li %r10, 0
	stb %r10, 0(%r9)
	stb %r11, 1(%r9)
	li %r10, 108
	stb %r10, 2(%r9)
	li %r10, 101
	stb %r10, 3(%r9)
	li %r10, 110
	stb %r10, 4(%r9)
	li %r10, 103
	stb %r10, 5(%r9)
	li %r10, 116
	stb %r10, 6(%r9)
	li %r10, 104
	stb %r10, 7(%r9)
	li %r10, 8
	stb %r10, 8(%r9)
	li %r10, 0
	stb %r10, 9(%r9)
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	ld %r5, 264(%r12)
	addi %r5, %r5, 1104
	li %r6, 32
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 264(%r12)
	addi %r5, %r5, 1024
	li %r6, 10
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	li %r5, 74
	ld %r6, 280(%r12)
	rldicr %r6, %r6, 5, 58
	ld %r10, 264(%r12)
	addi %r10, %r10, 1136
	add %r6, %r6, %r10
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r11, 280(%r12)
	addi %r11, %r11, 1
	std %r11, 280(%r12)
	li %r9, 8
	subf %r9, %r11, %r9
	cmpldi %cr0, %r9, 0
	bne %cr0, 22b
	addi %r12, %r1, 0
	li %r10, 0
	std %r10, 280(%r12)
23:
	addi %r12, %r1, 0
	ld %r9, 264(%r12)
	addi %r9, %r9, 1024
	ld %r11, 280(%r12)
	ld %r8, 216(%r12)
	li %r10, 0
	stb %r10, 0(%r9)
	stb %r11, 1(%r9)
	li %r10, 109
	stb %r10, 2(%r9)
	li %r10, 101
	stb %r10, 3(%r9)
	li %r10, 115
	stb %r10, 4(%r9)
	li %r10, 115
	stb %r10, 5(%r9)
	li %r10, 97
	stb %r10, 6(%r9)
	li %r10, 103
	stb %r10, 7(%r9)
	li %r10, 101
	stb %r10, 8(%r9)
	rldicr %r10, %r8, 3, 60
	stb %r10, 10(%r9)
	rldicl %r10, %r10, 56, 8
	stb %r10, 9(%r9)
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	ld %r5, 264(%r12)
	addi %r5, %r5, 1104
	li %r6, 32
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 264(%r12)
	addi %r5, %r5, 1024
	li %r6, 11
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 264(%r12)
	addi %r3, %r3, 0
	ld %r4, 264(%r12)
	addi %r4, %r4, 96
	li %r5, 75
	ld %r6, 280(%r12)
	rldicr %r6, %r6, 5, 58
	ld %r10, 264(%r12)
	addi %r10, %r10, 1392
	add %r6, %r6, %r10
	ld %r7, 264(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r11, 280(%r12)
	addi %r11, %r11, 1
	std %r11, 280(%r12)
	ld %r9, 288(%r12)
	subf %r9, %r11, %r9
	cmpldi %cr0, %r9, 0
	bne %cr0, 23b
	addi %r12, %r1, 0
	ld %r9, 216(%r12)
	addi %r9, %r9, -11
	li %r8, 0
24:
	add %r8, %r8, %r8
	addi %r8, %r8, 1
	subf %r10, %r9, %r8
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	addi %r12, %r1, 0
	ld %r11, 264(%r12)
	addi %r11, %r11, 1136
	li %r7, 128
	li %r6, 0
25:
	lbz %r10, 0(%r11)
	rldicr %r10, %r10, 8, 55
	lbz %r5, 1(%r11)
	add %r10, %r10, %r5
	and %r10, %r10, %r8
	subf %r5, %r10, %r9
	rldicl %r5, %r5, 1, 63
	addi %r5, %r5, -1
	xor %r4, %r6, %r10
	and %r4, %r4, %r5
	xor %r6, %r6, %r4
	addi %r11, %r11, 2
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 25b
	addi %r12, %r1, 0
	ld %r11, 192(%r12)
	addi %r11, %r11, 2
	ld %r7, 216(%r12)
	addi %r7, %r7, -2
	li %r4, 2
	li %r5, 0
	li %r3, 0
	li %r0, 0
	li %r8, 0
	addi %r8, %r8, -1
26:
	lbz %r10, 0(%r11)
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	subf %r10, %r10, %r0
	xor %r9, %r5, %r8
	and %r9, %r9, %r10
	and %r9, %r9, %r4
	or %r3, %r3, %r9
	or %r5, %r5, %r10
	addi %r4, %r4, 1
	addi %r11, %r11, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 26b
	addi %r12, %r1, 0
	ld %r11, 192(%r12)
	ld %r7, 216(%r12)
	lbz %r10, 0(%r11)
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	subf %r10, %r10, %r0
	lbz %r9, 1(%r11)
	li %r4, 2
	xor %r9, %r9, %r4
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	subf %r9, %r9, %r0
	and %r10, %r10, %r9
	and %r5, %r5, %r10
	li %r4, 10
	subf %r9, %r4, %r3
	rldicl %r9, %r9, 1, 63
	subf %r9, %r9, %r0
	xor %r9, %r9, %r8
	and %r5, %r5, %r9
	subf %r9, %r3, %r7
	addi %r9, %r9, -1
	xor %r9, %r9, %r6
	and %r9, %r9, %r5
	xor %r6, %r6, %r9
	ld %r4, 272(%r12)
	li %r9, 1
	xor %r4, %r4, %r9
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	subf %r4, %r4, %r0
	subf %r3, %r6, %r7
	and %r6, %r6, %r4
	ld %r10, 200(%r12)
	std %r6, 0(%r10)
	ld %r10, 264(%r12)
	addi %r10, %r10, 1392
	li %r9, 0
27:
	lbz %r6, 0(%r11)
	lbz %r12, 0(%r10)
	xor %r6, %r6, %r12
	and %r6, %r6, %r5
	xor %r6, %r6, %r12
	subf %r12, %r3, %r9
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r0
	xor %r12, %r12, %r8
	and %r12, %r12, %r4
	and %r6, %r6, %r12
	stb %r6, 0(%r11)
	addi %r9, %r9, 1
	addi %r11, %r11, 1
	addi %r10, %r10, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 27b
	addi %r12, %r1, 0
	ld %r3, 272(%r12)
	ld %r0, 296(%r12)
	mtlr %r0
	addi %r1, %r1, 304
	blr
