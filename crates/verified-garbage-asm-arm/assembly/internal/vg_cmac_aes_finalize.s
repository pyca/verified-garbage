// The functions of `src/internal/vg_cmac_aes_finalize.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_finalize:
	ldr r12, [sp, #4]
	str r4, [r12, #2064]
	str r5, [r12, #2068]
	str lr, [r12, #2072]
	mov r5, r12
	ldr r4, [sp, #0]
	cmp r4, #16
	beq 20f
	mov r12, #0
	str r12, [r5, #2048]
	str r12, [r5, #2052]
	str r12, [r5, #2056]
	str r12, [r5, #2060]
	add lr, r5, #2048
	cmp r4, #0
	beq 22f
24:
	ldrb r12, [r3, #0]
	strb r12, [lr, #0]
	add r3, r3, #1
	add lr, lr, #1
	subs r4, r4, #1
	bne 24b
	b 23f
22:
23:
	mov r12, #128
	strb r12, [lr, #0]
	ldr r12, [r5, #2048]
	ldr lr, [r0, #256]
	eor r12, r12, lr
	str r12, [r5, #2048]
	ldr r12, [r5, #2052]
	ldr lr, [r0, #260]
	eor r12, r12, lr
	str r12, [r5, #2052]
	ldr r12, [r5, #2056]
	ldr lr, [r0, #264]
	eor r12, r12, lr
	str r12, [r5, #2056]
	ldr r12, [r5, #2060]
	ldr lr, [r0, #268]
	eor r12, r12, lr
	str r12, [r5, #2060]
	b 21f
20:
	ldr r12, [r3, #0]
	ldr lr, [r0, #240]
	eor r12, r12, lr
	str r12, [r5, #2048]
	ldr r12, [r3, #4]
	ldr lr, [r0, #244]
	eor r12, r12, lr
	str r12, [r5, #2052]
	ldr r12, [r3, #8]
	ldr lr, [r0, #248]
	eor r12, r12, lr
	str r12, [r5, #2056]
	ldr r12, [r3, #12]
	ldr lr, [r0, #252]
	eor r12, r12, lr
	str r12, [r5, #2060]
21:
	ldr r12, [r5, #2048]
	ldr lr, [r2, #0]
	eor r12, r12, lr
	str r12, [r5, #2048]
	ldr r12, [r5, #2052]
	ldr lr, [r2, #4]
	eor r12, r12, lr
	str r12, [r5, #2052]
	ldr r12, [r5, #2056]
	ldr lr, [r2, #8]
	eor r12, r12, lr
	str r12, [r5, #2056]
	ldr r12, [r5, #2060]
	ldr lr, [r2, #12]
	eor r12, r12, lr
	str r12, [r5, #2060]
	mov r12, #0
	str r12, [r2, #0]
	str r12, [r2, #4]
	str r12, [r2, #8]
	str r12, [r2, #12]
	mov r3, r2
	add r2, r5, #2048
	mov r4, #1
	push {r4, r5}
	bl {vg_aes_ctr32}
	ldr r4, [sp], #8
	ldr r4, [r5, #2064]
	ldr lr, [r5, #2072]
	ldr r5, [r5, #2068]
	bx lr
