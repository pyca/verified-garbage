// The functions of `src/internal/vg_x448_invert.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_invert:
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
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r29, 320(%r6)
	std %r30, 328(%r6)
	ld %r15, 280(%r6)
	ld %r16, 288(%r6)
	ld %r17, 296(%r6)
	ld %r18, 304(%r6)
	ld %r19, 312(%r6)
	ld %r20, 320(%r6)
	ld %r21, 328(%r6)
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
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r29, 320(%r6)
	std %r30, 328(%r6)
	ld %r15, 280(%r6)
	ld %r16, 288(%r6)
	ld %r17, 296(%r6)
	ld %r18, 304(%r6)
	ld %r19, 312(%r6)
	ld %r20, 320(%r6)
	ld %r21, 328(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
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
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	li %r12, 1
20:
	addi %r12, %r12, -1
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
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
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
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
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
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
	li %r12, 3
21:
	addi %r12, %r12, -1
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
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
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
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
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
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
	li %r12, 7
22:
	addi %r12, %r12, -1
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
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
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
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
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
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
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	li %r12, 15
23:
	addi %r12, %r12, -1
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
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
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
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
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
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
	li %r12, 31
24:
	addi %r12, %r12, -1
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
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
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
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
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 63
25:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 63
26:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 15
27:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 7
28:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 3
29:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 1
210:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
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
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
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
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	li %r12, 224
211:
	addi %r12, %r12, -1
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
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
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 1
212:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
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
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
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
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	blr
