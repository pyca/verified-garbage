// The functions of `src/internal/vg_ed448_r32_add_affine.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_r32_add_affine:
	ld %r15, 112(%r6)
	ld %r16, 120(%r6)
	ld %r17, 128(%r6)
	ld %r18, 136(%r6)
	ld %r19, 144(%r6)
	ld %r20, 152(%r6)
	ld %r21, 160(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r29, 432(%r6)
	std %r30, 440(%r6)
	ld %r15, 56(%r6)
	ld %r16, 64(%r6)
	ld %r17, 72(%r6)
	ld %r18, 80(%r6)
	ld %r19, 88(%r6)
	ld %r20, 96(%r6)
	ld %r21, 104(%r6)
	ld %r22, 168(%r6)
	ld %r23, 176(%r6)
	ld %r24, 184(%r6)
	ld %r25, 192(%r6)
	ld %r26, 200(%r6)
	ld %r27, 208(%r6)
	ld %r28, 216(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	ld %r15, 0(%r6)
	ld %r16, 8(%r6)
	ld %r17, 16(%r6)
	ld %r18, 24(%r6)
	ld %r19, 32(%r6)
	ld %r20, 40(%r6)
	ld %r21, 48(%r6)
	ld %r22, 224(%r6)
	ld %r23, 232(%r6)
	ld %r24, 240(%r6)
	ld %r25, 248(%r6)
	ld %r26, 256(%r6)
	ld %r27, 264(%r6)
	ld %r28, 272(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 504(%r6)
	ld %r23, 512(%r6)
	ld %r24, 520(%r6)
	ld %r25, 528(%r6)
	ld %r26, 536(%r6)
	ld %r27, 544(%r6)
	ld %r28, 552(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r7, 392(%r6)
	ld %r8, 560(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 400(%r6)
	ld %r8, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 408(%r6)
	ld %r8, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 416(%r6)
	ld %r8, 584(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 424(%r6)
	ld %r8, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 432(%r6)
	ld %r8, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 440(%r6)
	ld %r8, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 392(%r6)
	ld %r8, 560(%r6)
	addc %r7, %r7, %r8
	std %r7, 672(%r6)
	ld %r7, 400(%r6)
	ld %r8, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 408(%r6)
	ld %r8, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 416(%r6)
	ld %r8, 584(%r6)
	adde %r7, %r7, %r8
	std %r7, 696(%r6)
	ld %r7, 424(%r6)
	ld %r8, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 432(%r6)
	ld %r8, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 440(%r6)
	ld %r8, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	ld %r7, 56(%r6)
	ld %r8, 0(%r6)
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 64(%r6)
	ld %r8, 8(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 72(%r6)
	ld %r8, 16(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 80(%r6)
	ld %r8, 24(%r6)
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 88(%r6)
	ld %r8, 32(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 96(%r6)
	ld %r8, 40(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 104(%r6)
	ld %r8, 48(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	ld %r15, 728(%r6)
	ld %r16, 736(%r6)
	ld %r17, 744(%r6)
	ld %r18, 752(%r6)
	ld %r19, 760(%r6)
	ld %r20, 768(%r6)
	ld %r21, 776(%r6)
	ld %r22, 784(%r6)
	ld %r23, 792(%r6)
	ld %r24, 800(%r6)
	ld %r25, 808(%r6)
	ld %r26, 816(%r6)
	ld %r27, 824(%r6)
	ld %r28, 832(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 728(%r6)
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	std %r29, 768(%r6)
	std %r30, 776(%r6)
	ld %r15, 112(%r6)
	ld %r16, 120(%r6)
	ld %r17, 128(%r6)
	ld %r18, 136(%r6)
	ld %r19, 144(%r6)
	ld %r20, 152(%r6)
	ld %r21, 160(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 784(%r6)
	std %r8, 792(%r6)
	std %r9, 800(%r6)
	std %r10, 808(%r6)
	std %r11, 816(%r6)
	std %r29, 824(%r6)
	std %r30, 832(%r6)
	ld %r7, 728(%r6)
	ld %r8, 448(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r8, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r8, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r8, 472(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	ld %r7, 728(%r6)
	ld %r8, 504(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r8, 512(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r8, 520(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r8, 528(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 536(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 544(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 552(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	ld %r15, 784(%r6)
	ld %r16, 792(%r6)
	ld %r17, 800(%r6)
	ld %r18, 808(%r6)
	ld %r19, 816(%r6)
	ld %r20, 824(%r6)
	ld %r21, 832(%r6)
	ld %r22, 728(%r6)
	ld %r23, 736(%r6)
	ld %r24, 744(%r6)
	ld %r25, 752(%r6)
	ld %r26, 760(%r6)
	ld %r27, 768(%r6)
	ld %r28, 776(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 56(%r6)
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	std %r29, 96(%r6)
	std %r30, 104(%r6)
	ld %r15, 112(%r6)
	ld %r16, 120(%r6)
	ld %r17, 128(%r6)
	ld %r18, 136(%r6)
	ld %r19, 144(%r6)
	ld %r20, 152(%r6)
	ld %r21, 160(%r6)
	ld %r22, 672(%r6)
	ld %r23, 680(%r6)
	ld %r24, 688(%r6)
	ld %r25, 696(%r6)
	ld %r26, 704(%r6)
	ld %r27, 712(%r6)
	ld %r28, 720(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 784(%r6)
	std %r8, 792(%r6)
	std %r9, 800(%r6)
	std %r10, 808(%r6)
	std %r11, 816(%r6)
	std %r29, 824(%r6)
	std %r30, 832(%r6)
	ld %r7, 504(%r6)
	ld %r8, 448(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 512(%r6)
	ld %r8, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 520(%r6)
	ld %r8, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 528(%r6)
	ld %r8, 472(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 536(%r6)
	ld %r8, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 544(%r6)
	ld %r8, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 552(%r6)
	ld %r8, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	ld %r15, 784(%r6)
	ld %r16, 792(%r6)
	ld %r17, 800(%r6)
	ld %r18, 808(%r6)
	ld %r19, 816(%r6)
	ld %r20, 824(%r6)
	ld %r21, 832(%r6)
	ld %r22, 728(%r6)
	ld %r23, 736(%r6)
	ld %r24, 744(%r6)
	ld %r25, 752(%r6)
	ld %r26, 760(%r6)
	ld %r27, 768(%r6)
	ld %r28, 776(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 0(%r6)
	std %r8, 8(%r6)
	std %r9, 16(%r6)
	std %r10, 24(%r6)
	std %r11, 32(%r6)
	std %r29, 40(%r6)
	std %r30, 48(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 672(%r6)
	ld %r23, 680(%r6)
	ld %r24, 688(%r6)
	ld %r25, 696(%r6)
	ld %r26, 704(%r6)
	ld %r27, 712(%r6)
	ld %r28, 720(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 112(%r6)
	std %r8, 120(%r6)
	std %r9, 128(%r6)
	std %r10, 136(%r6)
	std %r11, 144(%r6)
	std %r29, 152(%r6)
	std %r30, 160(%r6)
	blr
