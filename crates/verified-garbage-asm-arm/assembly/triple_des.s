// The functions of `src/triple_des.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_expand_key:
	sub sp, sp, #512
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	str lr, [r3, #32]
	ldr r4, [r0, #0]
	ldr r5, [r0, #4]
	rev r4, r4
	rev r5, r5
	mov r11, #0
	mov r10, #0
	mov lr, #1
	mov r12, r5
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #5
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #6
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #7
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #8
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #9
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #10
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #11
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #12
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #13
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #14
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #15
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #16
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #17
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #18
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #19
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #20
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #21
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #22
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #23
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #24
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #25
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #26
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #27
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #28
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #28
	and r12, r12, lr
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #6
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #7
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #8
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #9
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #10
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #11
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #12
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #13
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #14
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #15
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #16
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #17
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #18
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #19
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #20
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #21
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #22
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #23
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #24
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #25
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #26
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #27
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #28
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #28
	and r12, r12, lr
	eor r11, r11, r12
	mov r9, #0
	add r8, r2, #0
20:
	lsr r4, r9, #1
	cmp r4, #0
	beq 21f
	cmp r9, #8
	beq 23f
	cmp r9, #15
	beq 25f
	lsr r4, r10, #26
	ror r10, r10, #30
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #26
	ror r11, r11, #30
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
	b 26f
25:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
26:
	b 24f
23:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
24:
	b 22f
21:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
22:
	mov r4, #0
	mov r5, #0
	mov lr, #1
	mov r12, r10
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #17
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #19
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #20
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #21
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #22
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #23
	eor r5, r5, r12
	mov r12, r10
	and r12, r12, lr
	ror r12, r12, #24
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #25
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #26
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #27
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #28
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #29
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #30
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #31
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #24
	and r12, r12, lr
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #1
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #2
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #3
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #4
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #6
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #7
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #8
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #9
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #10
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #11
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #12
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #13
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #14
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #15
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #16
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #17
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #19
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #20
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #21
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #22
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #23
	eor r4, r4, r12
	mov r12, r11
	and r12, r12, lr
	ror r12, r12, #24
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #25
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #26
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #27
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #28
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #29
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #30
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #31
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #24
	and r12, r12, lr
	eor r4, r4, r12
	str r4, [r8, #0]
	str r5, [r8, #4]
	add r8, r8, #8
	add r9, r9, #1
	cmp r9, #16
	bne 20b
	ldr r4, [r0, #8]
	ldr r5, [r0, #12]
	rev r4, r4
	rev r5, r5
	mov r11, #0
	mov r10, #0
	mov lr, #1
	mov r12, r5
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #5
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #6
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #7
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #8
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #9
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #10
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #11
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #12
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #13
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #14
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #15
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #16
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #17
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #18
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #19
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #20
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #21
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #22
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #23
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #24
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #25
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #26
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #27
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #28
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #28
	and r12, r12, lr
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #6
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #7
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #8
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #9
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #10
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #11
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #12
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #13
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #14
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #15
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #16
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #17
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #18
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #19
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #20
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #21
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #22
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #23
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #24
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #25
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #26
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #27
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #28
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #28
	and r12, r12, lr
	eor r11, r11, r12
	mov r9, #0
	add r8, r2, #128
27:
	lsr r4, r9, #1
	cmp r4, #0
	beq 28f
	cmp r9, #8
	beq 210f
	cmp r9, #15
	beq 212f
	lsr r4, r10, #26
	ror r10, r10, #30
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #26
	ror r11, r11, #30
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
	b 213f
212:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
213:
	b 211f
210:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
211:
	b 29f
28:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
29:
	mov r4, #0
	mov r5, #0
	mov lr, #1
	mov r12, r10
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #17
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #19
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #20
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #21
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #22
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #23
	eor r5, r5, r12
	mov r12, r10
	and r12, r12, lr
	ror r12, r12, #24
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #25
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #26
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #27
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #28
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #29
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #30
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #31
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #24
	and r12, r12, lr
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #1
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #2
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #3
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #4
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #6
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #7
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #8
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #9
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #10
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #11
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #12
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #13
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #14
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #15
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #16
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #17
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #19
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #20
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #21
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #22
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #23
	eor r4, r4, r12
	mov r12, r11
	and r12, r12, lr
	ror r12, r12, #24
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #25
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #26
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #27
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #28
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #29
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #30
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #31
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #24
	and r12, r12, lr
	eor r4, r4, r12
	str r4, [r8, #0]
	str r5, [r8, #4]
	add r8, r8, #8
	add r9, r9, #1
	cmp r9, #16
	bne 27b
	cmp r1, #16
	beq 214f
	ldr r4, [r0, #16]
	ldr r5, [r0, #20]
	rev r4, r4
	rev r5, r5
	mov r11, #0
	mov r10, #0
	mov lr, #1
	mov r12, r5
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #5
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #6
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #7
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #8
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #9
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #10
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #11
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #31
	and r12, r12, lr
	ror r12, r12, #12
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #13
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #14
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #15
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #16
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #17
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #18
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #19
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #30
	and r12, r12, lr
	ror r12, r12, #20
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #21
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #22
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #23
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #24
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #25
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #26
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #27
	eor r10, r10, r12
	mov r12, r4
	lsr r12, r12, #29
	and r12, r12, lr
	ror r12, r12, #28
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #28
	and r12, r12, lr
	eor r10, r10, r12
	mov r12, r5
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #6
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #7
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #8
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #9
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #10
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #11
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #12
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #13
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #14
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #15
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #16
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #17
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #18
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #19
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #20
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #21
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #22
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #23
	eor r11, r11, r12
	mov r12, r5
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #24
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #25
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #26
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #27
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #28
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #29
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #30
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #31
	eor r11, r11, r12
	mov r12, r4
	lsr r12, r12, #28
	and r12, r12, lr
	eor r11, r11, r12
	mov r9, #0
	add r8, r2, #256
216:
	lsr r4, r9, #1
	cmp r4, #0
	beq 217f
	cmp r9, #8
	beq 219f
	cmp r9, #15
	beq 221f
	lsr r4, r10, #26
	ror r10, r10, #30
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #26
	ror r11, r11, #30
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
	b 222f
221:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
222:
	b 220f
219:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
220:
	b 218f
217:
	lsr r4, r10, #27
	ror r10, r10, #31
	eor r10, r10, r4
	lsl r10, r10, #4
	lsr r10, r10, #4
	lsr r4, r11, #27
	ror r11, r11, #31
	eor r11, r11, r4
	lsl r11, r11, #4
	lsr r11, r11, #4
218:
	mov r4, #0
	mov r5, #0
	mov lr, #1
	mov r12, r10
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #17
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #19
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #20
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #21
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #22
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #23
	eor r5, r5, r12
	mov r12, r10
	and r12, r12, lr
	ror r12, r12, #24
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #13
	and r12, r12, lr
	ror r12, r12, #25
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #26
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #27
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #18
	and r12, r12, lr
	ror r12, r12, #28
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #29
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #30
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #31
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #24
	and r12, r12, lr
	eor r5, r5, r12
	mov r12, r10
	lsr r12, r12, #2
	and r12, r12, lr
	ror r12, r12, #1
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #2
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #3
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #21
	and r12, r12, lr
	ror r12, r12, #4
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #5
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #6
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #7
	eor r4, r4, r12
	mov r12, r10
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #8
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #15
	and r12, r12, lr
	ror r12, r12, #9
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #4
	and r12, r12, lr
	ror r12, r12, #10
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #25
	and r12, r12, lr
	ror r12, r12, #11
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #19
	and r12, r12, lr
	ror r12, r12, #12
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #9
	and r12, r12, lr
	ror r12, r12, #13
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #1
	and r12, r12, lr
	ror r12, r12, #14
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #26
	and r12, r12, lr
	ror r12, r12, #15
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #16
	and r12, r12, lr
	ror r12, r12, #16
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #5
	and r12, r12, lr
	ror r12, r12, #17
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #11
	and r12, r12, lr
	ror r12, r12, #18
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #23
	and r12, r12, lr
	ror r12, r12, #19
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #8
	and r12, r12, lr
	ror r12, r12, #20
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #12
	and r12, r12, lr
	ror r12, r12, #21
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #7
	and r12, r12, lr
	ror r12, r12, #22
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #17
	and r12, r12, lr
	ror r12, r12, #23
	eor r4, r4, r12
	mov r12, r11
	and r12, r12, lr
	ror r12, r12, #24
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #22
	and r12, r12, lr
	ror r12, r12, #25
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #3
	and r12, r12, lr
	ror r12, r12, #26
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #10
	and r12, r12, lr
	ror r12, r12, #27
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #14
	and r12, r12, lr
	ror r12, r12, #28
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #6
	and r12, r12, lr
	ror r12, r12, #29
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #20
	and r12, r12, lr
	ror r12, r12, #30
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #27
	and r12, r12, lr
	ror r12, r12, #31
	eor r4, r4, r12
	mov r12, r11
	lsr r12, r12, #24
	and r12, r12, lr
	eor r4, r4, r12
	str r4, [r8, #0]
	str r5, [r8, #4]
	add r8, r8, #8
	add r9, r9, #1
	cmp r9, #16
	bne 216b
	b 215f
214:
	ldr r4, [r2, #0]
	ldr r5, [r2, #4]
	str r4, [r2, #256]
	str r5, [r2, #260]
	ldr r4, [r2, #8]
	ldr r5, [r2, #12]
	str r4, [r2, #264]
	str r5, [r2, #268]
	ldr r4, [r2, #16]
	ldr r5, [r2, #20]
	str r4, [r2, #272]
	str r5, [r2, #276]
	ldr r4, [r2, #24]
	ldr r5, [r2, #28]
	str r4, [r2, #280]
	str r5, [r2, #284]
	ldr r4, [r2, #32]
	ldr r5, [r2, #36]
	str r4, [r2, #288]
	str r5, [r2, #292]
	ldr r4, [r2, #40]
	ldr r5, [r2, #44]
	str r4, [r2, #296]
	str r5, [r2, #300]
	ldr r4, [r2, #48]
	ldr r5, [r2, #52]
	str r4, [r2, #304]
	str r5, [r2, #308]
	ldr r4, [r2, #56]
	ldr r5, [r2, #60]
	str r4, [r2, #312]
	str r5, [r2, #316]
	ldr r4, [r2, #64]
	ldr r5, [r2, #68]
	str r4, [r2, #320]
	str r5, [r2, #324]
	ldr r4, [r2, #72]
	ldr r5, [r2, #76]
	str r4, [r2, #328]
	str r5, [r2, #332]
	ldr r4, [r2, #80]
	ldr r5, [r2, #84]
	str r4, [r2, #336]
	str r5, [r2, #340]
	ldr r4, [r2, #88]
	ldr r5, [r2, #92]
	str r4, [r2, #344]
	str r5, [r2, #348]
	ldr r4, [r2, #96]
	ldr r5, [r2, #100]
	str r4, [r2, #352]
	str r5, [r2, #356]
	ldr r4, [r2, #104]
	ldr r5, [r2, #108]
	str r4, [r2, #360]
	str r5, [r2, #364]
	ldr r4, [r2, #112]
	ldr r5, [r2, #116]
	str r4, [r2, #368]
	str r5, [r2, #372]
	ldr r4, [r2, #120]
	ldr r5, [r2, #124]
	str r4, [r2, #376]
	str r5, [r2, #380]
215:
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	ldr lr, [r3, #32]
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	add sp, sp, #512
	bx lr

vg_triple_des_ecb_encrypt:
	sub sp, sp, #1024
	add r3, sp, #0
	str lr, [r3, #512]
	mov r12, r3
	mov r3, r2
	mov r2, r12
	cmp r3, #0
	beq 20f
22:
	bl {vg_triple_des_encrypt_block}
	add r1, r1, #8
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	ldr lr, [r2, #512]
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	add sp, sp, #1024
	bx lr

vg_triple_des_ecb_decrypt:
	sub sp, sp, #1024
	add r3, sp, #0
	str lr, [r3, #512]
	mov r12, r3
	mov r3, r2
	mov r2, r12
	cmp r3, #0
	beq 20f
22:
	bl {vg_triple_des_decrypt_block}
	add r1, r1, #8
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	ldr lr, [r2, #512]
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	add sp, sp, #1024
	bx lr
