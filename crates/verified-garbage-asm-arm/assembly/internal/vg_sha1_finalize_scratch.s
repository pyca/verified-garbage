// The functions of `src/internal/vg_sha1_finalize_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_finalize_scratch:
	ldr r12, [sp, #4]
	str r4, [r12, #112]
	str r5, [r12, #116]
	str r6, [r12, #120]
	str r7, [r12, #124]
	str r8, [r12, #128]
	str r9, [r12, #132]
	str r10, [r12, #136]
	str r11, [r12, #140]
	str lr, [r12, #144]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #63
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #20]
	add r7, r7, #1
	add r8, r7, #7
	lsr r8, r8, #6
20:
	mov r9, #64
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #56
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #20]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #76]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #80]
27:
	add r1, r0, #20
	mov r2, #1
	bl {vg_sha1_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	rev r9, r9
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	rev r9, r9
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	rev r9, r9
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	rev r9, r9
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	rev r9, r9
	str r9, [r6, #16]
	ldr r4, [r3, #112]
	ldr r5, [r3, #116]
	ldr r6, [r3, #120]
	ldr r7, [r3, #124]
	ldr r8, [r3, #128]
	ldr r9, [r3, #132]
	ldr r10, [r3, #136]
	ldr r11, [r3, #140]
	ldr lr, [r3, #144]
	bx lr
