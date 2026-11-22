// The functions of `src/seed_cfb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cfb128_encrypt:
	sub sp, sp, #80
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	ldr r9, [r5, #8]
	str r9, [r8, #48]
	ldr r9, [r5, #12]
	str r9, [r8, #52]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_seed_ecb_encrypt}
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #48]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #52]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r6, #0]
	str r9, [r8, #40]
	ldr r9, [r6, #4]
	str r9, [r8, #44]
	ldr r9, [r6, #8]
	str r9, [r8, #48]
	ldr r9, [r6, #12]
	str r9, [r8, #52]
	add r6, r6, #16
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r9, [r8, #48]
	str r9, [r5, #8]
	ldr r9, [r8, #52]
	str r9, [r5, #12]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add r12, sp, #8
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
	add sp, sp, #80
	sub sp, sp, #832
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #752]
	str r2, [r12, #756]
	add sp, sp, #832
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_seed_cfb128_decrypt:
	sub sp, sp, #80
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	ldr r9, [r5, #8]
	str r9, [r8, #48]
	ldr r9, [r5, #12]
	str r9, [r8, #52]
	cmp r7, #0
	sub sp, sp, #128
	lsr r9, r7, #3
	cmp r9, #0
	beq 20f
22:
	add r12, sp, #0
	ldr r9, [r8, #40]
	str r9, [r12, #0]
	ldr r9, [r8, #44]
	str r9, [r12, #4]
	ldr r9, [r8, #48]
	str r9, [r12, #8]
	ldr r9, [r8, #52]
	str r9, [r12, #12]
	ldr r9, [r6, #0]
	str r9, [r12, #16]
	ldr r9, [r6, #4]
	str r9, [r12, #20]
	ldr r9, [r6, #8]
	str r9, [r12, #24]
	ldr r9, [r6, #12]
	str r9, [r12, #28]
	ldr r9, [r6, #16]
	str r9, [r12, #32]
	ldr r9, [r6, #20]
	str r9, [r12, #36]
	ldr r9, [r6, #24]
	str r9, [r12, #40]
	ldr r9, [r6, #28]
	str r9, [r12, #44]
	ldr r9, [r6, #32]
	str r9, [r12, #48]
	ldr r9, [r6, #36]
	str r9, [r12, #52]
	ldr r9, [r6, #40]
	str r9, [r12, #56]
	ldr r9, [r6, #44]
	str r9, [r12, #60]
	ldr r9, [r6, #48]
	str r9, [r12, #64]
	ldr r9, [r6, #52]
	str r9, [r12, #68]
	ldr r9, [r6, #56]
	str r9, [r12, #72]
	ldr r9, [r6, #60]
	str r9, [r12, #76]
	ldr r9, [r6, #64]
	str r9, [r12, #80]
	ldr r9, [r6, #68]
	str r9, [r12, #84]
	ldr r9, [r6, #72]
	str r9, [r12, #88]
	ldr r9, [r6, #76]
	str r9, [r12, #92]
	ldr r9, [r6, #80]
	str r9, [r12, #96]
	ldr r9, [r6, #84]
	str r9, [r12, #100]
	ldr r9, [r6, #88]
	str r9, [r12, #104]
	ldr r9, [r6, #92]
	str r9, [r12, #108]
	ldr r9, [r6, #96]
	str r9, [r12, #112]
	ldr r9, [r6, #100]
	str r9, [r12, #116]
	ldr r9, [r6, #104]
	str r9, [r12, #120]
	ldr r9, [r6, #108]
	str r9, [r12, #124]
	ldr r9, [r6, #112]
	str r9, [r8, #40]
	ldr r9, [r6, #116]
	str r9, [r8, #44]
	ldr r9, [r6, #120]
	str r9, [r8, #48]
	ldr r9, [r6, #124]
	str r9, [r8, #52]
	ldr r9, [r6, #112]
	str r9, [r8, #56]
	ldr r9, [r6, #116]
	str r9, [r8, #60]
	ldr r9, [r6, #120]
	str r9, [r8, #64]
	ldr r9, [r6, #124]
	str r9, [r8, #68]
	mov r0, r4
	mov r1, r12
	mov r2, #8
	bl {vg_seed_ecb_encrypt}
	add r12, sp, #0
	ldr r9, [r6, #0]
	ldr r10, [r12, #0]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r12, #4]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r12, #8]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r12, #12]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r6, #16]
	ldr r10, [r12, #16]
	eor r9, r9, r10
	str r9, [r6, #16]
	ldr r9, [r6, #20]
	ldr r10, [r12, #20]
	eor r9, r9, r10
	str r9, [r6, #20]
	ldr r9, [r6, #24]
	ldr r10, [r12, #24]
	eor r9, r9, r10
	str r9, [r6, #24]
	ldr r9, [r6, #28]
	ldr r10, [r12, #28]
	eor r9, r9, r10
	str r9, [r6, #28]
	ldr r9, [r6, #32]
	ldr r10, [r12, #32]
	eor r9, r9, r10
	str r9, [r6, #32]
	ldr r9, [r6, #36]
	ldr r10, [r12, #36]
	eor r9, r9, r10
	str r9, [r6, #36]
	ldr r9, [r6, #40]
	ldr r10, [r12, #40]
	eor r9, r9, r10
	str r9, [r6, #40]
	ldr r9, [r6, #44]
	ldr r10, [r12, #44]
	eor r9, r9, r10
	str r9, [r6, #44]
	ldr r9, [r6, #48]
	ldr r10, [r12, #48]
	eor r9, r9, r10
	str r9, [r6, #48]
	ldr r9, [r6, #52]
	ldr r10, [r12, #52]
	eor r9, r9, r10
	str r9, [r6, #52]
	ldr r9, [r6, #56]
	ldr r10, [r12, #56]
	eor r9, r9, r10
	str r9, [r6, #56]
	ldr r9, [r6, #60]
	ldr r10, [r12, #60]
	eor r9, r9, r10
	str r9, [r6, #60]
	ldr r9, [r6, #64]
	ldr r10, [r12, #64]
	eor r9, r9, r10
	str r9, [r6, #64]
	ldr r9, [r6, #68]
	ldr r10, [r12, #68]
	eor r9, r9, r10
	str r9, [r6, #68]
	ldr r9, [r6, #72]
	ldr r10, [r12, #72]
	eor r9, r9, r10
	str r9, [r6, #72]
	ldr r9, [r6, #76]
	ldr r10, [r12, #76]
	eor r9, r9, r10
	str r9, [r6, #76]
	ldr r9, [r6, #80]
	ldr r10, [r12, #80]
	eor r9, r9, r10
	str r9, [r6, #80]
	ldr r9, [r6, #84]
	ldr r10, [r12, #84]
	eor r9, r9, r10
	str r9, [r6, #84]
	ldr r9, [r6, #88]
	ldr r10, [r12, #88]
	eor r9, r9, r10
	str r9, [r6, #88]
	ldr r9, [r6, #92]
	ldr r10, [r12, #92]
	eor r9, r9, r10
	str r9, [r6, #92]
	ldr r9, [r6, #96]
	ldr r10, [r12, #96]
	eor r9, r9, r10
	str r9, [r6, #96]
	ldr r9, [r6, #100]
	ldr r10, [r12, #100]
	eor r9, r9, r10
	str r9, [r6, #100]
	ldr r9, [r6, #104]
	ldr r10, [r12, #104]
	eor r9, r9, r10
	str r9, [r6, #104]
	ldr r9, [r6, #108]
	ldr r10, [r12, #108]
	eor r9, r9, r10
	str r9, [r6, #108]
	ldr r9, [r6, #112]
	ldr r10, [r12, #112]
	eor r9, r9, r10
	str r9, [r6, #112]
	ldr r9, [r6, #116]
	ldr r10, [r12, #116]
	eor r9, r9, r10
	str r9, [r6, #116]
	ldr r9, [r6, #120]
	ldr r10, [r12, #120]
	eor r9, r9, r10
	str r9, [r6, #120]
	ldr r9, [r6, #124]
	ldr r10, [r12, #124]
	eor r9, r9, r10
	str r9, [r6, #124]
	add r6, r6, #128
	sub r7, r7, #8
	lsr r9, r7, #3
	cmp r9, #0
	bne 22b
	b 21f
20:
21:
	lsr r9, r7, #2
	cmp r9, #0
	beq 23f
25:
	add r12, sp, #0
	ldr r9, [r8, #40]
	str r9, [r12, #0]
	ldr r9, [r8, #44]
	str r9, [r12, #4]
	ldr r9, [r8, #48]
	str r9, [r12, #8]
	ldr r9, [r8, #52]
	str r9, [r12, #12]
	ldr r9, [r6, #0]
	str r9, [r12, #16]
	ldr r9, [r6, #4]
	str r9, [r12, #20]
	ldr r9, [r6, #8]
	str r9, [r12, #24]
	ldr r9, [r6, #12]
	str r9, [r12, #28]
	ldr r9, [r6, #16]
	str r9, [r12, #32]
	ldr r9, [r6, #20]
	str r9, [r12, #36]
	ldr r9, [r6, #24]
	str r9, [r12, #40]
	ldr r9, [r6, #28]
	str r9, [r12, #44]
	ldr r9, [r6, #32]
	str r9, [r12, #48]
	ldr r9, [r6, #36]
	str r9, [r12, #52]
	ldr r9, [r6, #40]
	str r9, [r12, #56]
	ldr r9, [r6, #44]
	str r9, [r12, #60]
	ldr r9, [r6, #48]
	str r9, [r8, #40]
	ldr r9, [r6, #52]
	str r9, [r8, #44]
	ldr r9, [r6, #56]
	str r9, [r8, #48]
	ldr r9, [r6, #60]
	str r9, [r8, #52]
	ldr r9, [r6, #48]
	str r9, [r8, #56]
	ldr r9, [r6, #52]
	str r9, [r8, #60]
	ldr r9, [r6, #56]
	str r9, [r8, #64]
	ldr r9, [r6, #60]
	str r9, [r8, #68]
	mov r0, r4
	mov r1, r12
	mov r2, #4
	bl {vg_seed_ecb_encrypt}
	add r12, sp, #0
	ldr r9, [r6, #0]
	ldr r10, [r12, #0]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r12, #4]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r12, #8]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r12, #12]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r6, #16]
	ldr r10, [r12, #16]
	eor r9, r9, r10
	str r9, [r6, #16]
	ldr r9, [r6, #20]
	ldr r10, [r12, #20]
	eor r9, r9, r10
	str r9, [r6, #20]
	ldr r9, [r6, #24]
	ldr r10, [r12, #24]
	eor r9, r9, r10
	str r9, [r6, #24]
	ldr r9, [r6, #28]
	ldr r10, [r12, #28]
	eor r9, r9, r10
	str r9, [r6, #28]
	ldr r9, [r6, #32]
	ldr r10, [r12, #32]
	eor r9, r9, r10
	str r9, [r6, #32]
	ldr r9, [r6, #36]
	ldr r10, [r12, #36]
	eor r9, r9, r10
	str r9, [r6, #36]
	ldr r9, [r6, #40]
	ldr r10, [r12, #40]
	eor r9, r9, r10
	str r9, [r6, #40]
	ldr r9, [r6, #44]
	ldr r10, [r12, #44]
	eor r9, r9, r10
	str r9, [r6, #44]
	ldr r9, [r6, #48]
	ldr r10, [r12, #48]
	eor r9, r9, r10
	str r9, [r6, #48]
	ldr r9, [r6, #52]
	ldr r10, [r12, #52]
	eor r9, r9, r10
	str r9, [r6, #52]
	ldr r9, [r6, #56]
	ldr r10, [r12, #56]
	eor r9, r9, r10
	str r9, [r6, #56]
	ldr r9, [r6, #60]
	ldr r10, [r12, #60]
	eor r9, r9, r10
	str r9, [r6, #60]
	add r6, r6, #64
	sub r7, r7, #4
	lsr r9, r7, #2
	cmp r9, #0
	bne 25b
	b 24f
23:
24:
	lsr r9, r7, #1
	cmp r9, #0
	beq 26f
28:
	add r12, sp, #0
	ldr r9, [r8, #40]
	str r9, [r12, #0]
	ldr r9, [r8, #44]
	str r9, [r12, #4]
	ldr r9, [r8, #48]
	str r9, [r12, #8]
	ldr r9, [r8, #52]
	str r9, [r12, #12]
	ldr r9, [r6, #0]
	str r9, [r12, #16]
	ldr r9, [r6, #4]
	str r9, [r12, #20]
	ldr r9, [r6, #8]
	str r9, [r12, #24]
	ldr r9, [r6, #12]
	str r9, [r12, #28]
	ldr r9, [r6, #16]
	str r9, [r8, #40]
	ldr r9, [r6, #20]
	str r9, [r8, #44]
	ldr r9, [r6, #24]
	str r9, [r8, #48]
	ldr r9, [r6, #28]
	str r9, [r8, #52]
	ldr r9, [r6, #16]
	str r9, [r8, #56]
	ldr r9, [r6, #20]
	str r9, [r8, #60]
	ldr r9, [r6, #24]
	str r9, [r8, #64]
	ldr r9, [r6, #28]
	str r9, [r8, #68]
	mov r0, r4
	mov r1, r12
	mov r2, #2
	bl {vg_seed_ecb_encrypt}
	add r12, sp, #0
	ldr r9, [r6, #0]
	ldr r10, [r12, #0]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r12, #4]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r12, #8]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r12, #12]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r6, #16]
	ldr r10, [r12, #16]
	eor r9, r9, r10
	str r9, [r6, #16]
	ldr r9, [r6, #20]
	ldr r10, [r12, #20]
	eor r9, r9, r10
	str r9, [r6, #20]
	ldr r9, [r6, #24]
	ldr r10, [r12, #24]
	eor r9, r9, r10
	str r9, [r6, #24]
	ldr r9, [r6, #28]
	ldr r10, [r12, #28]
	eor r9, r9, r10
	str r9, [r6, #28]
	add r6, r6, #32
	sub r7, r7, #2
	lsr r9, r7, #1
	cmp r9, #0
	bne 28b
	b 27f
26:
27:
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
	add sp, sp, #128
	cmp r7, #0
	beq 29f
211:
	ldr r9, [r6, #0]
	str r9, [r8, #56]
	ldr r9, [r6, #4]
	str r9, [r8, #60]
	ldr r9, [r6, #8]
	str r9, [r8, #64]
	ldr r9, [r6, #12]
	str r9, [r8, #68]
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_seed_ecb_encrypt}
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #48]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #52]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r8, #56]
	str r9, [r8, #40]
	ldr r9, [r8, #60]
	str r9, [r8, #44]
	ldr r9, [r8, #64]
	str r9, [r8, #48]
	ldr r9, [r8, #68]
	str r9, [r8, #52]
	add r6, r6, #16
	subs r7, r7, #1
	bne 211b
	b 210f
29:
210:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r9, [r8, #48]
	str r9, [r5, #8]
	ldr r9, [r8, #52]
	str r9, [r5, #12]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add r12, sp, #8
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
	add sp, sp, #80
	sub sp, sp, #960
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #880]
	str r2, [r12, #884]
	add sp, sp, #960
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_seed_cfb128_encrypt_final:
	sub sp, sp, #80
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	ldr r9, [r5, #8]
	str r9, [r8, #48]
	ldr r9, [r5, #12]
	str r9, [r8, #52]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_seed_ecb_encrypt}
	lsr r9, r7, #4
	cmp r9, #0
	beq 23f
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #48]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #52]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r6, #0]
	str r9, [r8, #40]
	ldr r9, [r6, #4]
	str r9, [r8, #44]
	ldr r9, [r6, #8]
	str r9, [r8, #48]
	ldr r9, [r6, #12]
	str r9, [r8, #52]
	add r6, r6, #16
	subs r7, r7, #16
	b 24f
23:
	add r0, r8, #40
25:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 25b
24:
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r9, [r8, #48]
	str r9, [r5, #8]
	ldr r9, [r8, #52]
	str r9, [r5, #12]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add r12, sp, #8
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
	add sp, sp, #80
	sub sp, sp, #832
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #752]
	str r2, [r12, #756]
	add sp, sp, #832
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_seed_cfb128_decrypt_final:
	sub sp, sp, #80
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	ldr r9, [r5, #8]
	str r9, [r8, #48]
	ldr r9, [r5, #12]
	str r9, [r8, #52]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_seed_ecb_encrypt}
	lsr r9, r7, #4
	cmp r9, #0
	beq 23f
	ldr r9, [r6, #0]
	str r9, [r8, #56]
	ldr r9, [r6, #4]
	str r9, [r8, #60]
	ldr r9, [r6, #8]
	str r9, [r8, #64]
	ldr r9, [r6, #12]
	str r9, [r8, #68]
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #48]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #52]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r8, #56]
	str r9, [r8, #40]
	ldr r9, [r8, #60]
	str r9, [r8, #44]
	ldr r9, [r8, #64]
	str r9, [r8, #48]
	ldr r9, [r8, #68]
	str r9, [r8, #52]
	add r6, r6, #16
	subs r7, r7, #16
	b 24f
23:
	add r0, r8, #40
25:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 25b
24:
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r9, [r8, #48]
	str r9, [r5, #8]
	ldr r9, [r8, #52]
	str r9, [r5, #12]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add r12, sp, #8
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
	add sp, sp, #80
	sub sp, sp, #832
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #752]
	str r2, [r12, #756]
	add sp, sp, #832
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
