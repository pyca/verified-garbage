// The functions of `src/camellia_ctr.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr:
	sub sp, sp, #88
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #88]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
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
	mov r11, r1
	mov r5, r2
	mov r6, r3
	ldr r7, [sp, #0]
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
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #16]
	ldr r9, [r8, #44]
	str r9, [r12, #20]
	ldr r9, [r8, #48]
	str r9, [r12, #24]
	ldr r9, [r8, #52]
	str r9, [r12, #28]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #32]
	ldr r9, [r8, #44]
	str r9, [r12, #36]
	ldr r9, [r8, #48]
	str r9, [r12, #40]
	ldr r9, [r8, #52]
	str r9, [r12, #44]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #48]
	ldr r9, [r8, #44]
	str r9, [r12, #52]
	ldr r9, [r8, #48]
	str r9, [r12, #56]
	ldr r9, [r8, #52]
	str r9, [r12, #60]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #64]
	ldr r9, [r8, #44]
	str r9, [r12, #68]
	ldr r9, [r8, #48]
	str r9, [r12, #72]
	ldr r9, [r8, #52]
	str r9, [r12, #76]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #80]
	ldr r9, [r8, #44]
	str r9, [r12, #84]
	ldr r9, [r8, #48]
	str r9, [r12, #88]
	ldr r9, [r8, #52]
	str r9, [r12, #92]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #96]
	ldr r9, [r8, #44]
	str r9, [r12, #100]
	ldr r9, [r8, #48]
	str r9, [r12, #104]
	ldr r9, [r8, #52]
	str r9, [r12, #108]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #112]
	ldr r9, [r8, #44]
	str r9, [r12, #116]
	ldr r9, [r8, #48]
	str r9, [r12, #120]
	ldr r9, [r8, #52]
	str r9, [r12, #124]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	mov r0, r4
	mov r1, r11
	mov r2, r12
	mov r3, #8
	bl {vg_camellia_ecb_encrypt_entry}
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
	ldr r9, [r12, #112]
	str r9, [r8, #56]
	ldr r9, [r12, #116]
	str r9, [r8, #60]
	ldr r9, [r12, #120]
	str r9, [r8, #64]
	ldr r9, [r12, #124]
	str r9, [r8, #68]
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
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #16]
	ldr r9, [r8, #44]
	str r9, [r12, #20]
	ldr r9, [r8, #48]
	str r9, [r12, #24]
	ldr r9, [r8, #52]
	str r9, [r12, #28]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #32]
	ldr r9, [r8, #44]
	str r9, [r12, #36]
	ldr r9, [r8, #48]
	str r9, [r12, #40]
	ldr r9, [r8, #52]
	str r9, [r12, #44]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #48]
	ldr r9, [r8, #44]
	str r9, [r12, #52]
	ldr r9, [r8, #48]
	str r9, [r12, #56]
	ldr r9, [r8, #52]
	str r9, [r12, #60]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	mov r0, r4
	mov r1, r11
	mov r2, r12
	mov r3, #4
	bl {vg_camellia_ecb_encrypt_entry}
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
	ldr r9, [r12, #48]
	str r9, [r8, #56]
	ldr r9, [r12, #52]
	str r9, [r8, #60]
	ldr r9, [r12, #56]
	str r9, [r8, #64]
	ldr r9, [r12, #60]
	str r9, [r8, #68]
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
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	ldr r9, [r8, #40]
	str r9, [r12, #16]
	ldr r9, [r8, #44]
	str r9, [r12, #20]
	ldr r9, [r8, #48]
	str r9, [r12, #24]
	ldr r9, [r8, #52]
	str r9, [r12, #28]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
	mov r0, r4
	mov r1, r11
	mov r2, r12
	mov r3, #2
	bl {vg_camellia_ecb_encrypt_entry}
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
	ldr r9, [r12, #16]
	str r9, [r8, #56]
	ldr r9, [r12, #20]
	str r9, [r8, #60]
	ldr r9, [r12, #24]
	str r9, [r8, #64]
	ldr r9, [r12, #28]
	str r9, [r8, #68]
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
	ldr r9, [r8, #40]
	str r9, [r8, #56]
	ldr r9, [r8, #44]
	str r9, [r8, #60]
	ldr r9, [r8, #48]
	str r9, [r8, #64]
	ldr r9, [r8, #52]
	str r9, [r8, #68]
	mov r0, r4
	mov r1, r11
	add r2, r8, #56
	mov r3, #1
	bl {vg_camellia_ecb_encrypt_entry}
	ldr r9, [r6, #0]
	ldr r10, [r8, #56]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #60]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #64]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #68]
	eor r9, r9, r10
	str r9, [r6, #12]
	ldr r9, [r8, #52]
	rev r9, r9
	adds r9, r9, #1
	rev r9, r9
	str r9, [r8, #52]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #48]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #48]
	mov r10, #0
	adc r10, r10, #0
	ldr r9, [r8, #44]
	rev r9, r9
	adds r9, r9, r10
	rev r9, r9
	str r9, [r8, #44]
	ldr r9, [r8, #40]
	rev r9, r9
	adc r9, r9, #0
	rev r9, r9
	str r9, [r8, #40]
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
	add r12, sp, #12
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
	add sp, sp, #88
	sub sp, sp, #3040
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #2736]
	str r2, [r12, #2740]
	str r2, [r12, #2744]
	str r2, [r12, #2748]
	str r2, [r12, #2752]
	str r2, [r12, #2756]
	str r2, [r12, #2760]
	str r2, [r12, #2764]
	str r2, [r12, #2768]
	str r2, [r12, #2772]
	str r2, [r12, #2776]
	str r2, [r12, #2780]
	str r2, [r12, #2784]
	str r2, [r12, #2788]
	str r2, [r12, #2792]
	str r2, [r12, #2796]
	str r2, [r12, #2800]
	str r2, [r12, #2804]
	str r2, [r12, #2808]
	str r2, [r12, #2812]
	str r2, [r12, #2816]
	str r2, [r12, #2820]
	str r2, [r12, #2864]
	str r2, [r12, #2868]
	str r2, [r12, #2872]
	str r2, [r12, #2876]
	str r2, [r12, #2880]
	str r2, [r12, #2884]
	str r2, [r12, #2888]
	str r2, [r12, #2892]
	str r2, [r12, #2896]
	str r2, [r12, #2900]
	str r2, [r12, #2904]
	str r2, [r12, #2908]
	str r2, [r12, #2912]
	str r2, [r12, #2916]
	str r2, [r12, #2920]
	str r2, [r12, #2924]
	str r2, [r12, #2928]
	str r2, [r12, #2932]
	str r2, [r12, #2936]
	str r2, [r12, #2940]
	str r2, [r12, #2944]
	str r2, [r12, #2948]
	str r2, [r12, #2952]
	str r2, [r12, #2956]
	str r2, [r12, #2960]
	str r2, [r12, #3036]
	add sp, sp, #3040
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_camellia_ctr_final:
	sub sp, sp, #72
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #72]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
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
	lsr r12, r8, #4
	and r8, r8, #15
	add r7, r3, r12, lsl #4
	push {r12, lr}
	bl {vg_camellia_ctr_entry}
	ldr r12, [sp], #8
	cmp r8, #0
	beq 20f
	ldr r12, [sp, #4]
	mov r0, #0
	str r0, [r12, #40]
	str r0, [r12, #44]
	str r0, [r12, #48]
	str r0, [r12, #52]
	mov r0, r4
	mov r1, r5
	mov r2, r6
	add r3, r12, #40
	mov r12, #1
	push {r12, lr}
	bl {vg_camellia_ctr_entry}
	ldr r12, [sp], #8
	ldr r12, [sp, #4]
	add r0, r12, #40
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
	ldr r12, [sp, #4]
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	add r12, sp, #12
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
	add sp, sp, #72
	sub sp, sp, #3120
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #2736]
	str r2, [r12, #2740]
	str r2, [r12, #2744]
	str r2, [r12, #2748]
	str r2, [r12, #2752]
	str r2, [r12, #2756]
	str r2, [r12, #2760]
	str r2, [r12, #2764]
	str r2, [r12, #2768]
	str r2, [r12, #2772]
	str r2, [r12, #2776]
	str r2, [r12, #2780]
	str r2, [r12, #2784]
	str r2, [r12, #2788]
	str r2, [r12, #2792]
	str r2, [r12, #2796]
	str r2, [r12, #2800]
	str r2, [r12, #2804]
	str r2, [r12, #2808]
	str r2, [r12, #2812]
	str r2, [r12, #2816]
	str r2, [r12, #2820]
	str r2, [r12, #2864]
	str r2, [r12, #2868]
	str r2, [r12, #2872]
	str r2, [r12, #2876]
	str r2, [r12, #2880]
	str r2, [r12, #2884]
	str r2, [r12, #2888]
	str r2, [r12, #2892]
	str r2, [r12, #2896]
	str r2, [r12, #2900]
	str r2, [r12, #2904]
	str r2, [r12, #2908]
	str r2, [r12, #2912]
	str r2, [r12, #2916]
	str r2, [r12, #2920]
	str r2, [r12, #2924]
	str r2, [r12, #2928]
	str r2, [r12, #2932]
	str r2, [r12, #2936]
	str r2, [r12, #2940]
	str r2, [r12, #2944]
	str r2, [r12, #2948]
	str r2, [r12, #2952]
	str r2, [r12, #2956]
	str r2, [r12, #2960]
	str r2, [r12, #3036]
	str r2, [r12, #3040]
	str r2, [r12, #3044]
	str r2, [r12, #3048]
	str r2, [r12, #3052]
	str r2, [r12, #3056]
	str r2, [r12, #3116]
	add sp, sp, #3120
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
