// The functions of `src/blake2s.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_compress:
	ldr r12, [sp, #12]
	ldr r3, [sp, #0]
	str r3, [r12, #92]
	ldr r3, [sp, #4]
	str r3, [r12, #96]
	ldr r3, [sp, #8]
	str r4, [r12, #108]
	str r5, [r12, #112]
	str r6, [r12, #116]
	str r7, [r12, #120]
	str r8, [r12, #124]
	str r9, [r12, #128]
	str r10, [r12, #132]
	str r11, [r12, #136]
	str lr, [r12, #140]
	str r0, [r12, #80]
	str r1, [r12, #84]
	str r2, [r12, #88]
	mov lr, #0
	sub lr, lr, r3
	orr lr, lr, r3
	lsr lr, lr, #31
	mov r3, #0
	sub lr, r3, lr
	str lr, [r12, #100]
	str r3, [r12, #104]
	cmp r2, #0
	beq 20f
22:
	ldr r0, [r12, #84]
	ldr lr, [r0, #0]
	str lr, [r12, #0]
	ldr lr, [r0, #4]
	str lr, [r12, #4]
	ldr lr, [r0, #8]
	str lr, [r12, #8]
	ldr lr, [r0, #12]
	str lr, [r12, #12]
	ldr lr, [r0, #16]
	str lr, [r12, #16]
	ldr lr, [r0, #20]
	str lr, [r12, #20]
	ldr lr, [r0, #24]
	str lr, [r12, #24]
	ldr lr, [r0, #28]
	str lr, [r12, #28]
	ldr lr, [r0, #32]
	str lr, [r12, #32]
	ldr lr, [r0, #36]
	str lr, [r12, #36]
	ldr lr, [r0, #40]
	str lr, [r12, #40]
	ldr lr, [r0, #44]
	str lr, [r12, #44]
	ldr lr, [r0, #48]
	str lr, [r12, #48]
	ldr lr, [r0, #52]
	str lr, [r12, #52]
	ldr lr, [r0, #56]
	str lr, [r12, #56]
	ldr lr, [r0, #60]
	str lr, [r12, #60]
	add r0, r0, #64
	str r0, [r12, #84]
	ldr r11, [r12, #80]
	ldr r0, [r11, #0]
	ldr r1, [r11, #4]
	ldr r2, [r11, #8]
	ldr r3, [r11, #12]
	ldr r4, [r11, #16]
	ror r4, r4, #25
	ldr r5, [r11, #20]
	ror r5, r5, #25
	ldr r6, [r11, #24]
	ror r6, r6, #25
	ldr r7, [r11, #28]
	ror r7, r7, #25
	movw lr, #58983
	movt lr, #27145
	str lr, [r12, #64]
	movw lr, #44677
	movt lr, #47975
	str lr, [r12, #68]
	movw lr, #62322
	movt lr, #15470
	str lr, [r12, #72]
	movw lr, #62778
	movt lr, #42319
	str lr, [r12, #76]
	movw r8, #32593
	movt r8, #3666
	ldr lr, [r12, #92]
	eor r8, r8, lr, ror #24
	movw r9, #35995
	movt r9, #1384
	ldr lr, [r12, #96]
	eor r9, r9, lr, ror #24
	movw r10, #43807
	movt r10, #33753
	ldr lr, [r12, #100]
	eor r10, r10, lr, ror #24
	movw r11, #6491
	movt r11, #57549
	ldr lr, [r12, #104]
	eor r11, r11, lr, ror #24
	ldr lr, [r12, #0]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #4]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #8]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #12]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #16]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #20]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #24]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #28]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #32]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #36]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #40]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #44]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #48]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #52]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #56]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #60]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #56]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #40]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #16]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #32]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #36]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #60]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #52]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #24]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #4]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #48]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #0]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #8]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #44]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #28]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #20]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #12]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #44]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #32]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #48]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #0]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #20]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #8]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #60]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #52]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #40]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #56]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #12]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #24]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #28]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #4]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #36]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #16]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #28]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #36]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #12]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #4]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #52]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #48]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #44]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #56]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #8]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #24]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #20]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #40]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #16]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #0]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #60]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #32]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #36]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #0]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #20]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #28]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #8]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #16]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #40]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #60]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #56]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #4]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #44]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #48]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #24]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #32]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #12]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #52]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #8]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #48]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #24]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #40]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #0]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #44]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #32]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #12]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #16]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #52]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #28]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #20]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #60]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #56]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #4]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #36]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #48]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #20]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #4]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #60]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #56]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #52]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #16]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #40]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #0]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #28]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #24]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #12]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #36]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #8]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #32]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #44]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #52]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #44]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #28]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #56]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #48]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #4]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #12]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #36]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #20]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #0]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #60]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #16]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #32]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #24]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #8]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #40]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #24]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #60]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #56]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #36]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #44]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #12]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #0]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #32]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #48]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #8]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #52]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #28]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #4]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #16]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #40]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #20]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #40]
	add r0, r0, r4, ror #7
	add r0, r0, lr
	eor r8, r0, r8, ror #8
	ldr lr, [r12, #8]
	add r0, r0, lr
	ldr lr, [r12, #64]
	add lr, lr, r8, ror #16
	eor r4, lr, r4, ror #7
	add r0, r0, r4, ror #12
	eor r8, r0, r8, ror #16
	add lr, lr, r8, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #32]
	add r1, r1, r5, ror #7
	add r1, r1, lr
	eor r9, r1, r9, ror #8
	ldr lr, [r12, #16]
	add r1, r1, lr
	ldr lr, [r12, #68]
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #7
	add r1, r1, r5, ror #12
	eor r9, r1, r9, ror #16
	add lr, lr, r9, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #68]
	ldr lr, [r12, #28]
	add r2, r2, r6, ror #7
	add r2, r2, lr
	eor r10, r2, r10, ror #8
	ldr lr, [r12, #24]
	add r2, r2, lr
	ldr lr, [r12, #72]
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #7
	add r2, r2, r6, ror #12
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #4]
	add r3, r3, r7, ror #7
	add r3, r3, lr
	eor r11, r3, r11, ror #8
	ldr lr, [r12, #20]
	add r3, r3, lr
	ldr lr, [r12, #76]
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #7
	add r3, r3, r7, ror #12
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #60]
	add r0, r0, r5, ror #7
	add r0, r0, lr
	eor r11, r0, r11, ror #8
	ldr lr, [r12, #44]
	add r0, r0, lr
	ldr lr, [r12, #72]
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #7
	add r0, r0, r5, ror #12
	eor r11, r0, r11, ror #16
	add lr, lr, r11, ror #8
	eor r5, lr, r5, ror #12
	str lr, [r12, #72]
	ldr lr, [r12, #36]
	add r1, r1, r6, ror #7
	add r1, r1, lr
	eor r8, r1, r8, ror #8
	ldr lr, [r12, #56]
	add r1, r1, lr
	ldr lr, [r12, #76]
	add lr, lr, r8, ror #16
	eor r6, lr, r6, ror #7
	add r1, r1, r6, ror #12
	eor r8, r1, r8, ror #16
	add lr, lr, r8, ror #8
	eor r6, lr, r6, ror #12
	str lr, [r12, #76]
	ldr lr, [r12, #12]
	add r2, r2, r7, ror #7
	add r2, r2, lr
	eor r9, r2, r9, ror #8
	ldr lr, [r12, #48]
	add r2, r2, lr
	ldr lr, [r12, #64]
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #7
	add r2, r2, r7, ror #12
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #8
	eor r7, lr, r7, ror #12
	str lr, [r12, #64]
	ldr lr, [r12, #52]
	add r3, r3, r4, ror #7
	add r3, r3, lr
	eor r10, r3, r10, ror #8
	ldr lr, [r12, #0]
	add r3, r3, lr
	ldr lr, [r12, #68]
	add lr, lr, r10, ror #16
	eor r4, lr, r4, ror #7
	add r3, r3, r4, ror #12
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #8
	eor r4, lr, r4, ror #12
	str lr, [r12, #68]
	eor r4, r4, r8, ror #1
	eor r5, r5, r9, ror #1
	eor r6, r6, r10, ror #1
	eor r7, r7, r11, ror #1
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr lr, [r8, #16]
	eor lr, lr, r4, ror #7
	str lr, [r8, #16]
	ldr lr, [r8, #20]
	eor lr, lr, r5, ror #7
	str lr, [r8, #20]
	ldr lr, [r8, #24]
	eor lr, lr, r6, ror #7
	str lr, [r8, #24]
	ldr lr, [r8, #28]
	eor lr, lr, r7, ror #7
	str lr, [r8, #28]
	ldr lr, [r12, #64]
	eor r0, r0, lr
	ldr lr, [r8, #0]
	eor lr, lr, r0
	str lr, [r8, #0]
	ldr lr, [r12, #68]
	eor r1, r1, lr
	ldr lr, [r8, #4]
	eor lr, lr, r1
	str lr, [r8, #4]
	ldr lr, [r12, #72]
	eor r2, r2, lr
	ldr lr, [r8, #8]
	eor lr, lr, r2
	str lr, [r8, #8]
	ldr lr, [r12, #76]
	eor r3, r3, lr
	ldr lr, [r8, #12]
	eor lr, lr, r3
	str lr, [r8, #12]
	ldr r0, [r12, #92]
	ldr r1, [r12, #96]
	adds r0, r0, #64
	adc r1, r1, #0
	str r0, [r12, #92]
	str r1, [r12, #96]
	str r8, [r12, #80]
	str r9, [r12, #84]
	subs r10, r10, #1
	str r10, [r12, #88]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r12, #108]
	ldr r5, [r12, #112]
	ldr r6, [r12, #116]
	ldr r7, [r12, #120]
	ldr r8, [r12, #124]
	ldr r9, [r12, #128]
	ldr r10, [r12, #132]
	ldr r11, [r12, #136]
	ldr lr, [r12, #140]
	bx lr

vg_blake2s_init:
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #4]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #8]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #12]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #16]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #20]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #24]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #28]
	movw r12, #58983
	movt r12, #27400
	eor r12, r12, r3, lsl #8
	eor r12, r12, r1
	str r12, [r0, #0]
	cmp r3, #0
	beq 20f
	mov r12, #0
	str r12, [r0, #32]
	str r12, [r0, #36]
	str r12, [r0, #40]
	str r12, [r0, #44]
	str r12, [r0, #48]
	str r12, [r0, #52]
	str r12, [r0, #56]
	str r12, [r0, #60]
	str r12, [r0, #64]
	str r12, [r0, #68]
	str r12, [r0, #72]
	str r12, [r0, #76]
	str r12, [r0, #80]
	str r12, [r0, #84]
	str r12, [r0, #88]
	str r12, [r0, #92]
	add r1, r0, #32
22:
	ldrb r12, [r2, #0]
	strb r12, [r1, #0]
	add r2, r2, #1
	add r1, r1, #1
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	bx lr

vg_blake2s_update:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #512]
	str r5, [r12, #516]
	str r6, [r12, #520]
	str r7, [r12, #524]
	str r8, [r12, #528]
	str r9, [r12, #532]
	str r10, [r12, #536]
	str r11, [r12, #540]
	str lr, [r12, #544]
	mov r4, r0
	mov r5, r12
	ldr r6, [sp, #0]
	ldr r7, [sp, #4]
	mov r9, r2
	mov r10, r3
	sub r8, r9, #1
	and r8, r8, #63
	add r8, r8, #1
	orr r12, r9, r10
	cmp r12, #0
	beq 20f
	b 21f
20:
	mov r8, #0
21:
	cmp r8, #0
	beq 22f
	mov r11, #64
	sub r11, r11, r8
	lsr r12, r7, #6
	cmp r12, #0
	beq 24f
	b 25f
24:
	add r12, r7, r8
	lsr r12, r12, #6
	cmp r12, #0
	beq 26f
	b 27f
26:
	mov r11, r7
27:
25:
	sub r7, r7, r11
	adds r9, r9, r11
	adc r10, r10, #0
	cmp r11, #0
	beq 28f
210:
	ldrb r12, [r6, #0]
	add r1, r4, r8
	strb r12, [r1, #32]
	add r6, r6, #1
	add r8, r8, #1
	subs r11, r11, #1
	bne 210b
	b 29f
28:
29:
	b 23f
22:
23:
	mov r2, #0
	cmp r7, #0
	beq 211f
	cmp r8, #0
	beq 213f
	mov r2, #1
	b 214f
213:
214:
	b 212f
211:
212:
	mov r0, r4
	mov r12, #0
	mov lr, r5
	add r1, r4, #32
	mov r3, r9
	mov r11, r10
	push {r3, r11, r12, lr}
	bl {vg_blake2s_compress}
	ldr r3, [sp], #16
	cmp r7, #0
	beq 215f
	mov r8, #0
	sub r2, r7, #1
	lsr r2, r2, #6
	mov r1, r6
	b 216f
215:
	mov r2, #0
	mov r1, r4
216:
	mov r0, r4
	mov r12, #0
	mov lr, r5
	adds r3, r9, #64
	adc r11, r10, #0
	push {r3, r11, r12, lr}
	bl {vg_blake2s_compress}
	ldr r3, [sp], #16
	cmp r7, #0
	beq 217f
	sub r11, r7, #1
	and r11, r11, #63
	add r11, r11, #1
	sub r12, r7, r11
	add r6, r6, r12
	sub r7, r7, r12
	adds r9, r9, r12
	adc r10, r10, #0
	sub r7, r7, r11
	adds r9, r9, r11
	adc r10, r10, #0
	cmp r11, #0
	beq 219f
221:
	ldrb r12, [r6, #0]
	add r1, r4, r8
	strb r12, [r1, #32]
	add r6, r6, #1
	add r8, r8, #1
	subs r11, r11, #1
	bne 221b
	b 220f
219:
220:
	b 218f
217:
218:
	mov r3, r5
	ldr r4, [r3, #512]
	ldr r5, [r3, #516]
	ldr r6, [r3, #520]
	ldr r7, [r3, #524]
	ldr r8, [r3, #528]
	ldr r9, [r3, #532]
	ldr r10, [r3, #536]
	ldr r11, [r3, #540]
	ldr lr, [r3, #544]
	add sp, sp, #592
	bx lr

vg_blake2s_finalize:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #512]
	str r5, [r12, #516]
	str r6, [r12, #520]
	str r7, [r12, #524]
	str r8, [r12, #528]
	str r9, [r12, #532]
	str r10, [r12, #536]
	str r11, [r12, #540]
	str lr, [r12, #544]
	mov r4, r0
	mov r5, r12
	ldr r6, [sp, #0]
	mov r9, r2
	mov r10, r3
	sub r8, r9, #1
	and r8, r8, #63
	add r8, r8, #1
	orr r12, r9, r10
	cmp r12, #0
	beq 20f
	b 21f
20:
	mov r8, #0
21:
	mov r12, #0
	mov r11, #64
	subs r11, r11, r8
	beq 22f
24:
	add r1, r4, r8
	strb r12, [r1, #32]
	add r8, r8, #1
	subs r11, r11, #1
	bne 24b
	b 23f
22:
23:
	mov r0, r4
	add r1, r4, #32
	mov r2, #1
	mov r3, r9
	mov r11, r10
	mov r12, #1
	mov lr, r5
	push {r3, r11, r12, lr}
	bl {vg_blake2s_compress}
	ldr r3, [sp], #16
	ldr r12, [r4, #0]
	str r12, [r6, #0]
	ldr r12, [r4, #4]
	str r12, [r6, #4]
	ldr r12, [r4, #8]
	str r12, [r6, #8]
	ldr r12, [r4, #12]
	str r12, [r6, #12]
	ldr r12, [r4, #16]
	str r12, [r6, #16]
	ldr r12, [r4, #20]
	str r12, [r6, #20]
	ldr r12, [r4, #24]
	str r12, [r6, #24]
	ldr r12, [r4, #28]
	str r12, [r6, #28]
	mov r3, r5
	ldr r4, [r3, #512]
	ldr r5, [r3, #516]
	ldr r6, [r3, #520]
	ldr r7, [r3, #524]
	ldr r8, [r3, #528]
	ldr r9, [r3, #532]
	ldr r10, [r3, #536]
	ldr r11, [r3, #540]
	ldr lr, [r3, #544]
	add sp, sp, #592
	bx lr
