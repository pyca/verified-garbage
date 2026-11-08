// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
	.p2align 6

vg_rsa_pkcs1_encrypt_random:
	stdu %r1, -1216(%r1)
	addi %r12, %r1, 0
	std %r28, 144(%r12)
	std %r29, 152(%r12)
	std %r30, 160(%r12)
	std %r31, 168(%r12)
	mflr %r0
	std %r0, 176(%r12)
	or %r31, %r3, %r3
	or %r30, %r5, %r5
	or %r29, %r7, %r7
	ld %r0, 1312(%r12)
	subf %r28, %r0, %r7
	addi %r28, %r28, -3
	ld %r3, 1320(%r12)
	ld %r11, 1328(%r12)
	addi %r7, %r12, 192
	li %r4, 0
	li %r5, 0
	cmpldi %cr0, %r11, 0
	bne %cr0, 20f
	b 21f
20:
22:
	add %r12, %r3, %r4
	lbz %r0, 0(%r12)
	addi %r4, %r4, 1
	cmpldi %cr0, %r0, 0
	bne %cr0, 23f
	b 24f
23:
	add %r12, %r7, %r5
	stb %r0, 0(%r12)
	addi %r5, %r5, 1
24:
	subf %r12, %r5, %r28
	cmpldi %cr0, %r12, 0
	bne %cr0, 25f
	b 26f
25:
	subf %r12, %r4, %r11
26:
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
21:
	subf %r12, %r5, %r28
	cmpldi %cr0, %r12, 0
	beq %cr0, 27f
	or %r10, %r4, %r4
	or %r4, %r31, %r31
	or %r11, %r29, %r29
	li %r0, 0
29:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	addi %r12, %r1, 0
	addi %r4, %r12, 192
	or %r11, %r5, %r5
	cmpldi %cr0, %r11, 0
	bne %cr0, 210f
	b 211f
210:
212:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
211:
	addi %r12, %r28, 128
	subf %r0, %r10, %r12
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	li %r0, 0
	std %r0, 0(%r30)
	subf %r4, %r5, %r10
	addi %r4, %r4, -129
	rldicl %r4, %r4, 1, 63
	cmpldi %cr0, %r4, 0
	bne %cr0, 215f
	or %r0, %r12, %r12
	b 216f
215:
	add %r0, %r28, %r10
	subf %r0, %r5, %r0
216:
	std %r0, 8(%r30)
	li %r3, 0
	b 214f
213:
	std %r10, 0(%r30)
	li %r0, 0
	std %r0, 8(%r30)
	li %r3, 3
214:
	b 28f
27:
	std %r4, 0(%r30)
	li %r0, 0
	std %r0, 8(%r30)
	addi %r12, %r1, 0
	std %r7, 96(%r12)
	std %r28, 104(%r12)
	ld %r0, 1336(%r12)
	std %r0, 112(%r12)
	ld %r0, 1344(%r12)
	std %r0, 120(%r12)
	ld %r0, 1352(%r12)
	std %r0, 128(%r12)
	ld %r0, 1360(%r12)
	std %r0, 136(%r12)
	or %r3, %r31, %r31
	or %r4, %r29, %r29
	or %r5, %r6, %r6
	or %r6, %r29, %r29
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	or %r9, %r10, %r10
	ld %r10, 1312(%r12)
	bl {vg_rsa_pkcs1_encrypt_precomputed}
	li %r5, 2
	subf %r5, %r3, %r5
	addi %r12, %r1, 0
	addi %r4, %r12, 192
	or %r11, %r28, %r28
	li %r0, 0
217:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	or %r3, %r5, %r5
28:
	addi %r12, %r1, 0
	ld %r0, 176(%r12)
	mtlr %r0
	ld %r28, 144(%r12)
	ld %r29, 152(%r12)
	ld %r30, 160(%r12)
	ld %r31, 168(%r12)
	addi %r1, %r1, 1216
	blr
	.p2align 6
