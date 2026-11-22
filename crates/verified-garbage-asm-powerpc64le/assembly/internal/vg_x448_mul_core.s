// The functions of `src/internal/vg_x448_mul_core.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_mul_core:
	addi %r12, %r4, 0
	addi %r0, %r5, 0
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
	blr
