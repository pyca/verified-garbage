// The functions of `src/internal/vg_secp256k1_mul_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_mul_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	std %r15, 3840(%r3)
	std %r16, 3848(%r3)
	std %r17, 3856(%r3)
	std %r18, 3864(%r3)
	std %r19, 3872(%r3)
	std %r20, 3880(%r3)
	std %r21, 3888(%r3)
	std %r22, 3896(%r3)
	std %r23, 3904(%r3)
	std %r24, 3912(%r3)
	lis %r24, 19213
	ori %r24, %r24, 65382
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 21896
	ori %r24, %r24, 45375
	li %r15, 0
	li %r16, 0
	li %r17, 0
	li %r18, 0
	li %r19, 0
	ld %r20, 0(%r6)
	ld %r21, 8(%r6)
	ld %r22, 16(%r6)
	ld %r23, 24(%r6)
	lis %r6, -16430
	ori %r6, %r6, 24204
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 53302
	ori %r6, %r6, 16705
	lis %r7, -17746
	ori %r7, %r7, 56550
	rldicr %r7, %r7, 32, 31
	oris %r7, %r7, 44872
	ori %r7, %r7, 41019
	lis %r10, -1
	ori %r10, %r10, 65535
	rldicr %r10, %r10, 32, 31
	oris %r10, %r10, 65535
	ori %r10, %r10, 65534
	lis %r0, -1
	ori %r0, %r0, 65535
	li %r8, 4
20:
	ld %r9, 0(%r5)
	mulld %r11, %r9, %r20
	addc %r15, %r15, %r11
	mulld %r11, %r9, %r21
	adde %r16, %r16, %r11
	mulld %r11, %r9, %r22
	adde %r17, %r17, %r11
	mulld %r11, %r9, %r23
	adde %r18, %r18, %r11
	addze %r19, %r19
	li %r12, 0
	addze %r12, %r12
	mulhdu %r11, %r9, %r20
	addc %r16, %r16, %r11
	mulhdu %r11, %r9, %r21
	adde %r17, %r17, %r11
	mulhdu %r11, %r9, %r22
	adde %r18, %r18, %r11
	mulhdu %r11, %r9, %r23
	adde %r19, %r19, %r11
	addze %r12, %r12
	mulld %r9, %r15, %r24
	mulld %r11, %r9, %r6
	addc %r15, %r15, %r11
	mulld %r11, %r9, %r7
	adde %r16, %r16, %r11
	mulld %r11, %r9, %r10
	adde %r17, %r17, %r11
	mulld %r11, %r9, %r0
	adde %r18, %r18, %r11
	addze %r19, %r19
	addze %r12, %r12
	mulhdu %r11, %r9, %r6
	addc %r15, %r16, %r11
	mulhdu %r11, %r9, %r7
	adde %r16, %r17, %r11
	mulhdu %r11, %r9, %r10
	adde %r17, %r18, %r11
	mulhdu %r11, %r9, %r0
	adde %r18, %r19, %r11
	addze %r19, %r12
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	subfc %r20, %r6, %r15
	subfe %r21, %r7, %r16
	subfe %r22, %r10, %r17
	subfe %r23, %r0, %r18
	addze %r10, %r19
	li %r11, 0
	subf %r10, %r10, %r11
	xor %r12, %r20, %r15
	and %r12, %r12, %r10
	xor %r11, %r15, %r12
	std %r11, 0(%r4)
	xor %r12, %r21, %r16
	and %r12, %r12, %r10
	xor %r11, %r16, %r12
	std %r11, 8(%r4)
	xor %r12, %r22, %r17
	and %r12, %r12, %r10
	xor %r11, %r17, %r12
	std %r11, 16(%r4)
	xor %r12, %r23, %r18
	and %r12, %r12, %r10
	xor %r11, %r18, %r12
	std %r11, 24(%r4)
	ld %r15, 3840(%r3)
	ld %r16, 3848(%r3)
	ld %r17, 3856(%r3)
	ld %r18, 3864(%r3)
	ld %r19, 3872(%r3)
	ld %r20, 3880(%r3)
	ld %r21, 3888(%r3)
	ld %r22, 3896(%r3)
	ld %r23, 3904(%r3)
	ld %r24, 3912(%r3)
	blr
