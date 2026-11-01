// The functions of `src/aes_xts.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt:
	ldr r12, [sp, #4]
	str r4, [r12, #2064]
	str r5, [r12, #2068]
	str r6, [r12, #2072]
	str r7, [r12, #2076]
	str r8, [r12, #2080]
	str r9, [r12, #2084]
	str lr, [r12, #2092]
	str r10, [r12, #2088]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	ldr r8, [sp, #0]
	mov r10, r12
	cmp r8, #0
	beq 20f
22:
	ldr r12, [r7, #0]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r7, #12]
	mov r0, r4
	mov r1, r5
	mov r2, r7
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	ldr r12, [r7, #0]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r7, #12]
	ldr r0, [r6, #0]
	ldr r1, [r6, #4]
	ldr r2, [r6, #8]
	ldr r3, [r6, #12]
	mov r12, #0
	sub r12, r12, r3, lsr #31
	and r12, r12, #135
	lsl lr, r0, #1
	eor lr, lr, r12
	str lr, [r6, #0]
	lsl lr, r1, #1
	orr lr, lr, r0, lsr #31
	str lr, [r6, #4]
	lsl lr, r2, #1
	orr lr, lr, r1, lsr #31
	str lr, [r6, #8]
	lsl lr, r3, #1
	orr lr, lr, r2, lsr #31
	str lr, [r6, #12]
	add r7, r7, #16
	subs r8, r8, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r10, #2064]
	ldr r5, [r10, #2068]
	ldr r6, [r10, #2072]
	ldr r7, [r10, #2076]
	ldr r8, [r10, #2080]
	ldr r9, [r10, #2084]
	ldr lr, [r10, #2092]
	ldr r10, [r10, #2088]
	bx lr

vg_aes_xts_decrypt:
	ldr r12, [sp, #4]
	str r4, [r12, #2064]
	str r5, [r12, #2068]
	str r6, [r12, #2072]
	str r7, [r12, #2076]
	str r8, [r12, #2080]
	str r9, [r12, #2084]
	str lr, [r12, #2092]
	str r10, [r12, #2088]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	ldr r8, [sp, #0]
	mov r10, r12
	cmp r8, #0
	beq 20f
22:
	ldr r12, [r7, #0]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r7, #12]
	mov r0, r4
	mov r1, r5
	mov r2, r7
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_decrypt_blocks}
	ldr r12, [sp], #8
	ldr r12, [r7, #0]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r7, #12]
	ldr r0, [r6, #0]
	ldr r1, [r6, #4]
	ldr r2, [r6, #8]
	ldr r3, [r6, #12]
	mov r12, #0
	sub r12, r12, r3, lsr #31
	and r12, r12, #135
	lsl lr, r0, #1
	eor lr, lr, r12
	str lr, [r6, #0]
	lsl lr, r1, #1
	orr lr, lr, r0, lsr #31
	str lr, [r6, #4]
	lsl lr, r2, #1
	orr lr, lr, r1, lsr #31
	str lr, [r6, #8]
	lsl lr, r3, #1
	orr lr, lr, r2, lsr #31
	str lr, [r6, #12]
	add r7, r7, #16
	subs r8, r8, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r10, #2064]
	ldr r5, [r10, #2068]
	ldr r6, [r10, #2072]
	ldr r7, [r10, #2076]
	ldr r8, [r10, #2080]
	ldr r9, [r10, #2084]
	ldr lr, [r10, #2092]
	ldr r10, [r10, #2088]
	bx lr

vg_aes_xts_encrypt_unit:
	ldr r12, [sp, #8]
	str r4, [r12, #2208]
	str r5, [r12, #2212]
	str r6, [r12, #2216]
	str r7, [r12, #2220]
	str r9, [r12, #2224]
	str lr, [r12, #2228]
	str r8, [r12, #2232]
	mov r8, r12
	mov r4, r0
	mov r5, r2
	ldr r9, [sp, #0]
	ldr r7, [sp, #4]
	ldr r12, [r3, #0]
	ldr lr, [r3, #4]
	ldr r0, [r3, #8]
	ldr r2, [r3, #12]
	str r12, [r8, #2176]
	str lr, [r8, #2180]
	str r0, [r8, #2184]
	str r2, [r8, #2188]
	mov r12, #0
	str r12, [r8, #2192]
	str r12, [r8, #2196]
	str r12, [r8, #2200]
	str r12, [r8, #2204]
	mov r0, r1
	mov r1, r5
	add r2, r8, #2192
	add r3, r8, #2176
	mov r12, #1
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_encrypt}
	ldr r12, [sp], #8
	mov r0, r4
	mov r1, r5
	add r2, r8, #2176
	mov r3, r9
	lsr r12, r7, #4
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_encrypt}
	ldr r12, [sp], #8
	lsr r0, r7, #4
	lsl r0, r0, #4
	subs r1, r7, r0
	beq 20f
	add r2, r9, r0
	sub r2, r2, #16
22:
	ldrb r3, [r2, #0]
	ldrb r12, [r2, #16]
	strb r12, [r2, #0]
	strb r3, [r2, #16]
	add r2, r2, #1
	subs r1, r1, #1
	bne 22b
	add r3, r9, r0
	sub r3, r3, #16
	mov r0, r4
	mov r1, r5
	add r2, r8, #2176
	mov r12, #1
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_encrypt}
	ldr r12, [sp], #8
	b 21f
20:
21:
	ldr r4, [r8, #2208]
	ldr r5, [r8, #2212]
	ldr r6, [r8, #2216]
	ldr r7, [r8, #2220]
	ldr r9, [r8, #2224]
	ldr lr, [r8, #2228]
	ldr r8, [r8, #2232]
	bx lr

vg_aes_xts_decrypt_unit:
	ldr r12, [sp, #8]
	str r4, [r12, #2208]
	str r5, [r12, #2212]
	str r6, [r12, #2216]
	str r7, [r12, #2220]
	str r9, [r12, #2224]
	str lr, [r12, #2228]
	str r8, [r12, #2232]
	mov r8, r12
	mov r4, r0
	mov r5, r2
	ldr r9, [sp, #0]
	ldr r7, [sp, #4]
	ldr r12, [r3, #0]
	ldr lr, [r3, #4]
	ldr r0, [r3, #8]
	ldr r2, [r3, #12]
	str r12, [r8, #2176]
	str lr, [r8, #2180]
	str r0, [r8, #2184]
	str r2, [r8, #2188]
	mov r12, #0
	str r12, [r8, #2192]
	str r12, [r8, #2196]
	str r12, [r8, #2200]
	str r12, [r8, #2204]
	mov r0, r1
	mov r1, r5
	add r2, r8, #2192
	add r3, r8, #2176
	mov r12, #1
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_encrypt}
	ldr r12, [sp], #8
	lsr r0, r7, #4
	lsl r0, r0, #4
	subs r1, r7, r0
	beq 20f
	mov r0, r4
	mov r1, r5
	add r2, r8, #2176
	mov r3, r9
	lsr r12, r7, #4
	mov lr, r8
	sub r12, r12, #1
	push {r12, lr}
	bl {vg_aes_xts_decrypt}
	ldr r12, [sp], #8
	add r6, r8, #2192
	ldr r0, [r8, #2176]
	ldr r1, [r8, #2180]
	ldr r2, [r8, #2184]
	ldr r3, [r8, #2188]
	str r0, [r8, #2192]
	str r1, [r8, #2196]
	str r2, [r8, #2200]
	str r3, [r8, #2204]
	ldr r0, [r6, #0]
	ldr r1, [r6, #4]
	ldr r2, [r6, #8]
	ldr r3, [r6, #12]
	mov r12, #0
	sub r12, r12, r3, lsr #31
	and r12, r12, #135
	lsl lr, r0, #1
	eor lr, lr, r12
	str lr, [r6, #0]
	lsl lr, r1, #1
	orr lr, lr, r0, lsr #31
	str lr, [r6, #4]
	lsl lr, r2, #1
	orr lr, lr, r1, lsr #31
	str lr, [r6, #8]
	lsl lr, r3, #1
	orr lr, lr, r2, lsr #31
	str lr, [r6, #12]
	lsr r0, r7, #4
	lsl r0, r0, #4
	subs r1, r7, r0
	add r3, r9, r0
	sub r3, r3, #16
	mov r0, r4
	mov r1, r5
	add r2, r8, #2192
	mov r12, #1
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_decrypt}
	ldr r12, [sp], #8
	lsr r0, r7, #4
	lsl r0, r0, #4
	subs r1, r7, r0
	add r2, r9, r0
	sub r2, r2, #16
22:
	ldrb r3, [r2, #0]
	ldrb r12, [r2, #16]
	strb r12, [r2, #0]
	strb r3, [r2, #16]
	add r2, r2, #1
	subs r1, r1, #1
	bne 22b
	add r3, r9, r0
	sub r3, r3, #16
	mov r0, r4
	mov r1, r5
	add r2, r8, #2176
	mov r12, #1
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_decrypt}
	ldr r12, [sp], #8
	b 21f
20:
	mov r0, r4
	mov r1, r5
	add r2, r8, #2176
	mov r3, r9
	lsr r12, r7, #4
	mov lr, r8
	push {r12, lr}
	bl {vg_aes_xts_decrypt}
	ldr r12, [sp], #8
21:
	ldr r4, [r8, #2208]
	ldr r5, [r8, #2212]
	ldr r6, [r8, #2216]
	ldr r7, [r8, #2220]
	ldr r9, [r8, #2224]
	ldr lr, [r8, #2228]
	ldr r8, [r8, #2232]
	bx lr
