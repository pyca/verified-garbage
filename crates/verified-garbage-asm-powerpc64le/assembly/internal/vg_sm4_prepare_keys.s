// The functions of `src/internal/vg_sm4_prepare_keys.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_prepare_keys:
	or %r8, %r5, %r5
	std %r14, 3072(%r8)
	std %r15, 3080(%r8)
	std %r16, 3088(%r8)
	std %r17, 3096(%r8)
	std %r18, 3104(%r8)
	std %r19, 3112(%r8)
	std %r20, 3120(%r8)
	std %r21, 3128(%r8)
	std %r22, 3136(%r8)
	std %r23, 3144(%r8)
	std %r24, 3152(%r8)
	std %r25, 3160(%r8)
	std %r26, 3168(%r8)
	std %r27, 3176(%r8)
	std %r28, 3184(%r8)
	std %r29, 3192(%r8)
	std %r30, 3200(%r8)
	std %r31, 3208(%r8)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 255
	std %r22, 384(%r8)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65280
	std %r22, 392(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 400(%r8)
	cmpldi %cr0, %r4, 0
	bne %cr0, 20f
	b 21f
20:
	addi %r10, %r8, 3008
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_dec}
	mtlr %r9
	addi %r11, %r8, 3072
21:
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	b 23f
22:
	addi %r10, %r8, 1024
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	mflr %r9
	bl {vg_sm4_key_pairs_enc}
	mtlr %r9
	addi %r11, %r8, 3072
23:
	ld %r14, 3072(%r8)
	ld %r15, 3080(%r8)
	ld %r16, 3088(%r8)
	ld %r17, 3096(%r8)
	ld %r18, 3104(%r8)
	ld %r19, 3112(%r8)
	ld %r20, 3120(%r8)
	ld %r21, 3128(%r8)
	ld %r22, 3136(%r8)
	ld %r23, 3144(%r8)
	ld %r24, 3152(%r8)
	ld %r25, 3160(%r8)
	ld %r26, 3168(%r8)
	ld %r27, 3176(%r8)
	ld %r28, 3184(%r8)
	ld %r29, 3192(%r8)
	ld %r30, 3200(%r8)
	ld %r31, 3208(%r8)
	blr
