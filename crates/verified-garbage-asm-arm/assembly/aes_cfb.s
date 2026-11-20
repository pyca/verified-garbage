// The functions of `src/aes_cfb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_encrypt:
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
	mov r0, r4
	mov r1, r5
	mov r2, r10
	bl {vg_aes_blocks_keys}
22:
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks_keyed}
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
	mov r12, #0
	str r12, [r6, #0]
	str r12, [r6, #4]
	str r12, [r6, #8]
	str r12, [r6, #12]
	ldr r12, [r6, #0]
	ldr lr, [r7, #0]
	eor r12, r12, lr
	str r12, [r6, #0]
	ldr r12, [r6, #4]
	ldr lr, [r7, #4]
	eor r12, r12, lr
	str r12, [r6, #4]
	ldr r12, [r6, #8]
	ldr lr, [r7, #8]
	eor r12, r12, lr
	str r12, [r6, #8]
	ldr r12, [r6, #12]
	ldr lr, [r7, #12]
	eor r12, r12, lr
	str r12, [r6, #12]
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
	sub sp, sp, #8
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	add sp, sp, #8
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_aes_cfb128_decrypt:
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
	lsr r12, r8, #2
	cmp r12, #0
	beq 20f
22:
	mov r12, #0
	str r12, [r10, #2096]
	str r12, [r10, #2100]
	str r12, [r10, #2104]
	str r12, [r10, #2108]
	ldr r12, [r10, #2096]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r10, #2096]
	ldr r12, [r10, #2100]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r10, #2100]
	ldr r12, [r10, #2104]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r10, #2104]
	ldr r12, [r10, #2108]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r10, #2108]
	mov r12, #0
	str r12, [r10, #2112]
	str r12, [r10, #2116]
	str r12, [r10, #2120]
	str r12, [r10, #2124]
	ldr r12, [r10, #2112]
	ldr lr, [r7, #0]
	eor r12, r12, lr
	str r12, [r10, #2112]
	ldr r12, [r10, #2116]
	ldr lr, [r7, #4]
	eor r12, r12, lr
	str r12, [r10, #2116]
	ldr r12, [r10, #2120]
	ldr lr, [r7, #8]
	eor r12, r12, lr
	str r12, [r10, #2120]
	ldr r12, [r10, #2124]
	ldr lr, [r7, #12]
	eor r12, r12, lr
	str r12, [r10, #2124]
	mov r12, #0
	str r12, [r10, #2128]
	str r12, [r10, #2132]
	str r12, [r10, #2136]
	str r12, [r10, #2140]
	ldr r12, [r10, #2128]
	ldr lr, [r7, #16]
	eor r12, r12, lr
	str r12, [r10, #2128]
	ldr r12, [r10, #2132]
	ldr lr, [r7, #20]
	eor r12, r12, lr
	str r12, [r10, #2132]
	ldr r12, [r10, #2136]
	ldr lr, [r7, #24]
	eor r12, r12, lr
	str r12, [r10, #2136]
	ldr r12, [r10, #2140]
	ldr lr, [r7, #28]
	eor r12, r12, lr
	str r12, [r10, #2140]
	mov r12, #0
	str r12, [r10, #2144]
	str r12, [r10, #2148]
	str r12, [r10, #2152]
	str r12, [r10, #2156]
	ldr r12, [r10, #2144]
	ldr lr, [r7, #32]
	eor r12, r12, lr
	str r12, [r10, #2144]
	ldr r12, [r10, #2148]
	ldr lr, [r7, #36]
	eor r12, r12, lr
	str r12, [r10, #2148]
	ldr r12, [r10, #2152]
	ldr lr, [r7, #40]
	eor r12, r12, lr
	str r12, [r10, #2152]
	ldr r12, [r10, #2156]
	ldr lr, [r7, #44]
	eor r12, r12, lr
	str r12, [r10, #2156]
	mov r12, #0
	str r12, [r6, #0]
	str r12, [r6, #4]
	str r12, [r6, #8]
	str r12, [r6, #12]
	ldr r12, [r6, #0]
	ldr lr, [r7, #48]
	eor r12, r12, lr
	str r12, [r6, #0]
	ldr r12, [r6, #4]
	ldr lr, [r7, #52]
	eor r12, r12, lr
	str r12, [r6, #4]
	ldr r12, [r6, #8]
	ldr lr, [r7, #56]
	eor r12, r12, lr
	str r12, [r6, #8]
	ldr r12, [r6, #12]
	ldr lr, [r7, #60]
	eor r12, r12, lr
	str r12, [r6, #12]
	mov r0, r4
	mov r1, r5
	add r2, r10, #2096
	mov r3, #4
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	ldr r12, [r7, #0]
	ldr lr, [r10, #2096]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r10, #2100]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r10, #2104]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r10, #2108]
	eor r12, r12, lr
	str r12, [r7, #12]
	ldr r12, [r7, #16]
	ldr lr, [r10, #2112]
	eor r12, r12, lr
	str r12, [r7, #16]
	ldr r12, [r7, #20]
	ldr lr, [r10, #2116]
	eor r12, r12, lr
	str r12, [r7, #20]
	ldr r12, [r7, #24]
	ldr lr, [r10, #2120]
	eor r12, r12, lr
	str r12, [r7, #24]
	ldr r12, [r7, #28]
	ldr lr, [r10, #2124]
	eor r12, r12, lr
	str r12, [r7, #28]
	ldr r12, [r7, #32]
	ldr lr, [r10, #2128]
	eor r12, r12, lr
	str r12, [r7, #32]
	ldr r12, [r7, #36]
	ldr lr, [r10, #2132]
	eor r12, r12, lr
	str r12, [r7, #36]
	ldr r12, [r7, #40]
	ldr lr, [r10, #2136]
	eor r12, r12, lr
	str r12, [r7, #40]
	ldr r12, [r7, #44]
	ldr lr, [r10, #2140]
	eor r12, r12, lr
	str r12, [r7, #44]
	ldr r12, [r7, #48]
	ldr lr, [r10, #2144]
	eor r12, r12, lr
	str r12, [r7, #48]
	ldr r12, [r7, #52]
	ldr lr, [r10, #2148]
	eor r12, r12, lr
	str r12, [r7, #52]
	ldr r12, [r7, #56]
	ldr lr, [r10, #2152]
	eor r12, r12, lr
	str r12, [r7, #56]
	ldr r12, [r7, #60]
	ldr lr, [r10, #2156]
	eor r12, r12, lr
	str r12, [r7, #60]
	add r7, r7, #64
	sub r8, r8, #4
	lsr r12, r8, #2
	cmp r12, #0
	bne 22b
	b 21f
20:
21:
	lsr r12, r8, #1
	cmp r12, #0
	beq 23f
25:
	mov r12, #0
	str r12, [r10, #2096]
	str r12, [r10, #2100]
	str r12, [r10, #2104]
	str r12, [r10, #2108]
	ldr r12, [r10, #2096]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r10, #2096]
	ldr r12, [r10, #2100]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r10, #2100]
	ldr r12, [r10, #2104]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r10, #2104]
	ldr r12, [r10, #2108]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r10, #2108]
	mov r12, #0
	str r12, [r10, #2112]
	str r12, [r10, #2116]
	str r12, [r10, #2120]
	str r12, [r10, #2124]
	ldr r12, [r10, #2112]
	ldr lr, [r7, #0]
	eor r12, r12, lr
	str r12, [r10, #2112]
	ldr r12, [r10, #2116]
	ldr lr, [r7, #4]
	eor r12, r12, lr
	str r12, [r10, #2116]
	ldr r12, [r10, #2120]
	ldr lr, [r7, #8]
	eor r12, r12, lr
	str r12, [r10, #2120]
	ldr r12, [r10, #2124]
	ldr lr, [r7, #12]
	eor r12, r12, lr
	str r12, [r10, #2124]
	mov r12, #0
	str r12, [r6, #0]
	str r12, [r6, #4]
	str r12, [r6, #8]
	str r12, [r6, #12]
	ldr r12, [r6, #0]
	ldr lr, [r7, #16]
	eor r12, r12, lr
	str r12, [r6, #0]
	ldr r12, [r6, #4]
	ldr lr, [r7, #20]
	eor r12, r12, lr
	str r12, [r6, #4]
	ldr r12, [r6, #8]
	ldr lr, [r7, #24]
	eor r12, r12, lr
	str r12, [r6, #8]
	ldr r12, [r6, #12]
	ldr lr, [r7, #28]
	eor r12, r12, lr
	str r12, [r6, #12]
	mov r0, r4
	mov r1, r5
	add r2, r10, #2096
	mov r3, #2
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	ldr r12, [r7, #0]
	ldr lr, [r10, #2096]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r10, #2100]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r10, #2104]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r10, #2108]
	eor r12, r12, lr
	str r12, [r7, #12]
	ldr r12, [r7, #16]
	ldr lr, [r10, #2112]
	eor r12, r12, lr
	str r12, [r7, #16]
	ldr r12, [r7, #20]
	ldr lr, [r10, #2116]
	eor r12, r12, lr
	str r12, [r7, #20]
	ldr r12, [r7, #24]
	ldr lr, [r10, #2120]
	eor r12, r12, lr
	str r12, [r7, #24]
	ldr r12, [r7, #28]
	ldr lr, [r10, #2124]
	eor r12, r12, lr
	str r12, [r7, #28]
	add r7, r7, #32
	sub r8, r8, #2
	lsr r12, r8, #1
	cmp r12, #0
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
28:
	mov r0, r4
	mov r1, r5
	mov r2, r6
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
	ldr r12, [r6, #0]
	ldr lr, [r7, #0]
	eor r12, r12, lr
	str r12, [r6, #0]
	ldr r12, [r6, #4]
	ldr lr, [r7, #4]
	eor r12, r12, lr
	str r12, [r6, #4]
	ldr r12, [r6, #8]
	ldr lr, [r7, #8]
	eor r12, r12, lr
	str r12, [r6, #8]
	ldr r12, [r6, #12]
	ldr lr, [r7, #12]
	eor r12, r12, lr
	str r12, [r6, #12]
	add r7, r7, #16
	subs r8, r8, #1
	bne 28b
	b 27f
26:
27:
	ldr r4, [r10, #2064]
	ldr r5, [r10, #2068]
	ldr r6, [r10, #2072]
	ldr r7, [r10, #2076]
	ldr r8, [r10, #2080]
	ldr r9, [r10, #2084]
	ldr lr, [r10, #2092]
	ldr r10, [r10, #2088]
	sub sp, sp, #8
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	add sp, sp, #8
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_aes_cfb128_encrypt_final:
	sub sp, sp, #56
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #56]
	str lr, [r12, #0]
	ldr lr, [sp, #60]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	ldr r8, [sp, #0]
	ldr r10, [sp, #4]
	lsr r12, r8, #4
	and r8, r8, #15
	add r7, r3, r12, lsl #4
	mov lr, r10
	push {r12, lr}
	bl {vg_aes_cfb128_encrypt_entry}
	ldr r12, [sp], #8
	cmp r8, #0
	beq 20f
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	mov r0, r6
	mov r6, r7
	mov r7, r8
22:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r12, [sp, #8]
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	add r12, sp, #16
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
	add sp, sp, #56
	sub sp, sp, #72
	add r12, sp, #0
	mov r2, #0
	mov r3, #2
23:
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
	bne 23b
	str r2, [r12, #0]
	str r2, [r12, #4]
	add sp, sp, #72
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_aes_cfb128_decrypt_final:
	sub sp, sp, #56
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #56]
	str lr, [r12, #0]
	ldr lr, [sp, #60]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	ldr r8, [sp, #0]
	ldr r10, [sp, #4]
	lsr r12, r8, #4
	and r8, r8, #15
	add r7, r3, r12, lsl #4
	mov lr, r10
	push {r12, lr}
	bl {vg_aes_cfb128_decrypt_entry}
	ldr r12, [sp], #8
	cmp r8, #0
	beq 20f
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	mov r0, r6
	mov r6, r7
	mov r7, r8
22:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r12, [sp, #8]
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	add r12, sp, #16
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
	add sp, sp, #56
	sub sp, sp, #72
	add r12, sp, #0
	mov r2, #0
	mov r3, #2
23:
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
	bne 23b
	str r2, [r12, #0]
	str r2, [r12, #4]
	add sp, sp, #72
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
