// The functions of `src/internal/vg_md5_finalize_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_finalize_scratch:
	ldr r12, [sp, #4]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #63
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #16]
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
	strb r12, [r1, #16]
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
	lsl r9, r4, #3
	str r9, [r0, #72]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	str r9, [r0, #76]
27:
	add r1, r0, #16
	mov r2, #1
	bl {vg_md5_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r4, [r3, #64]
	ldr r5, [r3, #68]
	ldr r6, [r3, #72]
	ldr r7, [r3, #76]
	ldr r8, [r3, #80]
	ldr r9, [r3, #84]
	ldr r10, [r3, #88]
	ldr r11, [r3, #92]
	ldr lr, [r3, #96]
	bx lr
