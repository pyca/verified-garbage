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
	add sp, sp, #512
	sub sp, sp, #512
	add r12, sp, #0
	mov r2, #0
	mov r3, #16
223:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 223b
	add sp, sp, #512
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_triple_des_ecb_encrypt:
	push {r4, lr}
	mov r4, lr
	bl {vg_triple_des_ecb_encrypt_core}
	mov lr, r4
	ldr r4, [sp], #8
	sub sp, sp, #1040
	add r12, sp, #0
	mov r2, #0
	mov r3, #32
20:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 20b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #1040
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_triple_des_ecb_decrypt:
	push {r4, lr}
	mov r4, lr
	bl {vg_triple_des_ecb_decrypt_core}
	mov lr, r4
	ldr r4, [sp], #8
	sub sp, sp, #1040
	add r12, sp, #0
	mov r2, #0
	mov r3, #32
20:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 20b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #1040
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
