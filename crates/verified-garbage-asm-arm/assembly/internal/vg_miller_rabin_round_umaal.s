// The functions of `src/internal/vg_miller_rabin_round_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #9
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
20:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 20b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
21:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 21b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
22:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 22b
	mov r1, #14
	str r1, [r8, #140]
23:
	ldr r0, [sp, #0]
	mov r2, #6
	mov r3, #6
	mov r12, #5
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
24:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 24b
	mov r0, r5
25:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	cmp lr, #16
	beq 26f
	cmp lr, #32
	beq 28f
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
210:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 210b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	b 29f
28:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r3, [r12, #56]
	ldr r6, [r0, #60]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	ldr r3, [r12, #60]
	ldr r10, [r0, #64]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #56]
	umaal r6, r8, r5, r2
	str r6, [r0, #56]
	ldr r3, [r12, #64]
	ldr r6, [r0, #68]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #60]
	umaal r10, r8, r5, r2
	str r10, [r0, #60]
	ldr r3, [r12, #68]
	ldr r10, [r0, #72]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #64]
	umaal r6, r8, r5, r2
	str r6, [r0, #64]
	ldr r3, [r12, #72]
	ldr r6, [r0, #76]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #68]
	umaal r10, r8, r5, r2
	str r10, [r0, #68]
	ldr r3, [r12, #76]
	ldr r10, [r0, #80]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #72]
	umaal r6, r8, r5, r2
	str r6, [r0, #72]
	ldr r3, [r12, #80]
	ldr r6, [r0, #84]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #76]
	umaal r10, r8, r5, r2
	str r10, [r0, #76]
	ldr r3, [r12, #84]
	ldr r10, [r0, #88]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #80]
	umaal r6, r8, r5, r2
	str r6, [r0, #80]
	ldr r3, [r12, #88]
	ldr r6, [r0, #92]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #84]
	umaal r10, r8, r5, r2
	str r10, [r0, #84]
	ldr r3, [r12, #92]
	ldr r10, [r0, #96]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #88]
	umaal r6, r8, r5, r2
	str r6, [r0, #88]
	ldr r3, [r12, #96]
	ldr r6, [r0, #100]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #92]
	umaal r10, r8, r5, r2
	str r10, [r0, #92]
	ldr r3, [r12, #100]
	ldr r10, [r0, #104]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #96]
	umaal r6, r8, r5, r2
	str r6, [r0, #96]
	ldr r3, [r12, #104]
	ldr r6, [r0, #108]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #100]
	umaal r10, r8, r5, r2
	str r10, [r0, #100]
	ldr r3, [r12, #108]
	ldr r10, [r0, #112]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #104]
	umaal r6, r8, r5, r2
	str r6, [r0, #104]
	ldr r3, [r12, #112]
	ldr r6, [r0, #116]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #108]
	umaal r10, r8, r5, r2
	str r10, [r0, #108]
	ldr r3, [r12, #116]
	ldr r10, [r0, #120]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #112]
	umaal r6, r8, r5, r2
	str r6, [r0, #112]
	ldr r5, [r4, #116]
	umaal r10, r8, r5, r2
	str r10, [r0, #116]
	add r0, r0, #120
	add r12, r12, #120
	add r4, r4, #120
	subs lr, lr, #30
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
29:
	b 27f
26:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	add r0, r0, #56
	add r12, r12, #56
	add r4, r4, #56
	subs lr, lr, #14
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
27:
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 25b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
211:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 211b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
212:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 212b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr lr, [r8, #140]
	mov r0, #27
	sub r0, r0, lr
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
213:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 213b
	ldr r1, [r8, #140]
	subs r1, r1, #1
	str r1, [r8, #140]
	bne 23b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
214:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 214b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
215:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 215b
	mov r1, #0
	str r1, [r8, #136]
	lsl r1, r9, #3
	sub r1, r1, #16
	str r1, [r8, #140]
216:
	ldr r1, [r8, #140]
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr r1, r1, #3
	sub r1, r1, #1
	add r0, r0, r1, lsl #2
	ldr r2, [r0, #0]
	str r2, [r8, #116]
217:
	mov r1, #0
	str r1, [r8, #148]
	mov r1, #4
	str r1, [r8, #144]
218:
	ldr r0, [sp, #0]
	mov r2, #6
	mov r3, #6
	mov r12, #6
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
219:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 219b
	mov r0, r5
220:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	cmp lr, #16
	beq 221f
	cmp lr, #32
	beq 223f
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
225:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 225b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	b 224f
223:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r3, [r12, #56]
	ldr r6, [r0, #60]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	ldr r3, [r12, #60]
	ldr r10, [r0, #64]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #56]
	umaal r6, r8, r5, r2
	str r6, [r0, #56]
	ldr r3, [r12, #64]
	ldr r6, [r0, #68]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #60]
	umaal r10, r8, r5, r2
	str r10, [r0, #60]
	ldr r3, [r12, #68]
	ldr r10, [r0, #72]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #64]
	umaal r6, r8, r5, r2
	str r6, [r0, #64]
	ldr r3, [r12, #72]
	ldr r6, [r0, #76]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #68]
	umaal r10, r8, r5, r2
	str r10, [r0, #68]
	ldr r3, [r12, #76]
	ldr r10, [r0, #80]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #72]
	umaal r6, r8, r5, r2
	str r6, [r0, #72]
	ldr r3, [r12, #80]
	ldr r6, [r0, #84]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #76]
	umaal r10, r8, r5, r2
	str r10, [r0, #76]
	ldr r3, [r12, #84]
	ldr r10, [r0, #88]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #80]
	umaal r6, r8, r5, r2
	str r6, [r0, #80]
	ldr r3, [r12, #88]
	ldr r6, [r0, #92]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #84]
	umaal r10, r8, r5, r2
	str r10, [r0, #84]
	ldr r3, [r12, #92]
	ldr r10, [r0, #96]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #88]
	umaal r6, r8, r5, r2
	str r6, [r0, #88]
	ldr r3, [r12, #96]
	ldr r6, [r0, #100]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #92]
	umaal r10, r8, r5, r2
	str r10, [r0, #92]
	ldr r3, [r12, #100]
	ldr r10, [r0, #104]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #96]
	umaal r6, r8, r5, r2
	str r6, [r0, #96]
	ldr r3, [r12, #104]
	ldr r6, [r0, #108]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #100]
	umaal r10, r8, r5, r2
	str r10, [r0, #100]
	ldr r3, [r12, #108]
	ldr r10, [r0, #112]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #104]
	umaal r6, r8, r5, r2
	str r6, [r0, #104]
	ldr r3, [r12, #112]
	ldr r6, [r0, #116]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #108]
	umaal r10, r8, r5, r2
	str r10, [r0, #108]
	ldr r3, [r12, #116]
	ldr r10, [r0, #120]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #112]
	umaal r6, r8, r5, r2
	str r6, [r0, #112]
	ldr r5, [r4, #116]
	umaal r10, r8, r5, r2
	str r10, [r0, #116]
	add r0, r0, #120
	add r12, r12, #120
	add r4, r4, #120
	subs lr, lr, #30
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
224:
	b 222f
221:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	add r0, r0, #56
	add r12, r12, #56
	add r4, r4, #56
	subs lr, lr, #14
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
222:
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 220b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
226:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 226b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
227:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 227b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
228:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 228b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 218b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
229:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 229b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #1
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
230:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 230b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
231:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 231b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #3
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
232:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 232b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #4
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
233:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 233b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #5
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
234:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 234b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #6
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
235:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 235b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #7
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #18
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
236:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 236b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #8
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
237:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 237b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #9
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
238:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 238b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #10
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
239:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 239b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #11
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
240:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 240b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #12
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #23
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
241:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 241b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #13
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
242:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 242b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #14
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
243:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 243b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #15
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
244:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 244b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
245:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 245b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr r0, [sp, #0]
	mov r2, #6
	mov r3, #6
	mov r12, #5
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
246:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 246b
	mov r0, r5
247:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	cmp lr, #16
	beq 248f
	cmp lr, #32
	beq 250f
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
252:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 252b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	b 251f
250:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r3, [r12, #56]
	ldr r6, [r0, #60]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	ldr r3, [r12, #60]
	ldr r10, [r0, #64]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #56]
	umaal r6, r8, r5, r2
	str r6, [r0, #56]
	ldr r3, [r12, #64]
	ldr r6, [r0, #68]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #60]
	umaal r10, r8, r5, r2
	str r10, [r0, #60]
	ldr r3, [r12, #68]
	ldr r10, [r0, #72]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #64]
	umaal r6, r8, r5, r2
	str r6, [r0, #64]
	ldr r3, [r12, #72]
	ldr r6, [r0, #76]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #68]
	umaal r10, r8, r5, r2
	str r10, [r0, #68]
	ldr r3, [r12, #76]
	ldr r10, [r0, #80]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #72]
	umaal r6, r8, r5, r2
	str r6, [r0, #72]
	ldr r3, [r12, #80]
	ldr r6, [r0, #84]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #76]
	umaal r10, r8, r5, r2
	str r10, [r0, #76]
	ldr r3, [r12, #84]
	ldr r10, [r0, #88]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #80]
	umaal r6, r8, r5, r2
	str r6, [r0, #80]
	ldr r3, [r12, #88]
	ldr r6, [r0, #92]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #84]
	umaal r10, r8, r5, r2
	str r10, [r0, #84]
	ldr r3, [r12, #92]
	ldr r10, [r0, #96]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #88]
	umaal r6, r8, r5, r2
	str r6, [r0, #88]
	ldr r3, [r12, #96]
	ldr r6, [r0, #100]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #92]
	umaal r10, r8, r5, r2
	str r10, [r0, #92]
	ldr r3, [r12, #100]
	ldr r10, [r0, #104]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #96]
	umaal r6, r8, r5, r2
	str r6, [r0, #96]
	ldr r3, [r12, #104]
	ldr r6, [r0, #108]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #100]
	umaal r10, r8, r5, r2
	str r10, [r0, #100]
	ldr r3, [r12, #108]
	ldr r10, [r0, #112]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #104]
	umaal r6, r8, r5, r2
	str r6, [r0, #104]
	ldr r3, [r12, #112]
	ldr r6, [r0, #116]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #108]
	umaal r10, r8, r5, r2
	str r10, [r0, #108]
	ldr r3, [r12, #116]
	ldr r10, [r0, #120]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #112]
	umaal r6, r8, r5, r2
	str r6, [r0, #112]
	ldr r5, [r4, #116]
	umaal r10, r8, r5, r2
	str r10, [r0, #116]
	add r0, r0, #120
	add r12, r12, #120
	add r4, r4, #120
	subs lr, lr, #30
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
251:
	b 249f
248:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	add r0, r0, #56
	add r12, r12, #56
	add r4, r4, #56
	subs lr, lr, #14
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
249:
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 247b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
253:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 253b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
254:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 254b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #11
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
255:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 255b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #88]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
256:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 256b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #116]
	lsr r2, r1, #28
	sub r2, r2, #1
	lsr r2, r2, #31
	eor r3, r2, #1
	ldr r4, [r8, #88]
	ldr r5, [r8, #92]
	orr r4, r4, r5
	and r4, r4, r3
	ldr r5, [r8, #136]
	and r5, r5, r2
	orr r4, r4, r5
	str r4, [r8, #136]
	lsl r1, r1, #4
	str r1, [r8, #116]
	ldr r1, [r8, #140]
	sub r1, r1, #1
	str r1, [r8, #140]
	and r1, r1, #7
	cmp r1, #0
	bne 217b
	ldr r1, [r8, #140]
	cmp r1, #0
	bne 216b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	ldr r1, [r0, #0]
	ldr r2, [r0, #4]
	orr r1, r1, r2
	orr r1, r1, r1, lsr #16
	orr r1, r1, r1, lsr #8
	orr r1, r1, r1, lsr #4
	lsr r2, r1, #1
	and r2, r2, #1
	lsr r3, r1, #2
	and r3, r3, #1
	lsr r4, r1, #3
	and r4, r4, #1
	add r4, r4, r2
	add r4, r4, r2, lsl #1
	add r4, r4, r3, lsl #1
	str r4, [r8, #148]
	mov r1, #3
	str r1, [r8, #144]
257:
	ldr r0, [sp, #0]
	mov r2, #6
	mov r3, #6
	mov r12, #6
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
258:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 258b
	mov r0, r5
259:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	cmp lr, #16
	beq 260f
	cmp lr, #32
	beq 262f
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
264:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 264b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	b 263f
262:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r3, [r12, #56]
	ldr r6, [r0, #60]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	ldr r3, [r12, #60]
	ldr r10, [r0, #64]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #56]
	umaal r6, r8, r5, r2
	str r6, [r0, #56]
	ldr r3, [r12, #64]
	ldr r6, [r0, #68]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #60]
	umaal r10, r8, r5, r2
	str r10, [r0, #60]
	ldr r3, [r12, #68]
	ldr r10, [r0, #72]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #64]
	umaal r6, r8, r5, r2
	str r6, [r0, #64]
	ldr r3, [r12, #72]
	ldr r6, [r0, #76]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #68]
	umaal r10, r8, r5, r2
	str r10, [r0, #68]
	ldr r3, [r12, #76]
	ldr r10, [r0, #80]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #72]
	umaal r6, r8, r5, r2
	str r6, [r0, #72]
	ldr r3, [r12, #80]
	ldr r6, [r0, #84]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #76]
	umaal r10, r8, r5, r2
	str r10, [r0, #76]
	ldr r3, [r12, #84]
	ldr r10, [r0, #88]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #80]
	umaal r6, r8, r5, r2
	str r6, [r0, #80]
	ldr r3, [r12, #88]
	ldr r6, [r0, #92]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #84]
	umaal r10, r8, r5, r2
	str r10, [r0, #84]
	ldr r3, [r12, #92]
	ldr r10, [r0, #96]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #88]
	umaal r6, r8, r5, r2
	str r6, [r0, #88]
	ldr r3, [r12, #96]
	ldr r6, [r0, #100]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #92]
	umaal r10, r8, r5, r2
	str r10, [r0, #92]
	ldr r3, [r12, #100]
	ldr r10, [r0, #104]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #96]
	umaal r6, r8, r5, r2
	str r6, [r0, #96]
	ldr r3, [r12, #104]
	ldr r6, [r0, #108]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #100]
	umaal r10, r8, r5, r2
	str r10, [r0, #100]
	ldr r3, [r12, #108]
	ldr r10, [r0, #112]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #104]
	umaal r6, r8, r5, r2
	str r6, [r0, #104]
	ldr r3, [r12, #112]
	ldr r6, [r0, #116]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #108]
	umaal r10, r8, r5, r2
	str r10, [r0, #108]
	ldr r3, [r12, #116]
	ldr r10, [r0, #120]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #112]
	umaal r6, r8, r5, r2
	str r6, [r0, #112]
	ldr r5, [r4, #116]
	umaal r10, r8, r5, r2
	str r10, [r0, #116]
	add r0, r0, #120
	add r12, r12, #120
	add r4, r4, #120
	subs lr, lr, #30
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
263:
	b 261f
260:
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r3, [r12, #8]
	ldr r6, [r0, #12]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	ldr r3, [r12, #12]
	ldr r10, [r0, #16]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #8]
	umaal r6, r8, r5, r2
	str r6, [r0, #8]
	ldr r3, [r12, #16]
	ldr r6, [r0, #20]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #12]
	umaal r10, r8, r5, r2
	str r10, [r0, #12]
	ldr r3, [r12, #20]
	ldr r10, [r0, #24]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #16]
	umaal r6, r8, r5, r2
	str r6, [r0, #16]
	ldr r3, [r12, #24]
	ldr r6, [r0, #28]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #20]
	umaal r10, r8, r5, r2
	str r10, [r0, #20]
	ldr r3, [r12, #28]
	ldr r10, [r0, #32]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #24]
	umaal r6, r8, r5, r2
	str r6, [r0, #24]
	ldr r3, [r12, #32]
	ldr r6, [r0, #36]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #28]
	umaal r10, r8, r5, r2
	str r10, [r0, #28]
	ldr r3, [r12, #36]
	ldr r10, [r0, #40]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #32]
	umaal r6, r8, r5, r2
	str r6, [r0, #32]
	ldr r3, [r12, #40]
	ldr r6, [r0, #44]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #36]
	umaal r10, r8, r5, r2
	str r10, [r0, #36]
	ldr r3, [r12, #44]
	ldr r10, [r0, #48]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #40]
	umaal r6, r8, r5, r2
	str r6, [r0, #40]
	ldr r3, [r12, #48]
	ldr r6, [r0, #52]
	umaal r6, r7, r3, r1
	ldr r5, [r4, #44]
	umaal r10, r8, r5, r2
	str r10, [r0, #44]
	ldr r3, [r12, #52]
	ldr r10, [r0, #56]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #48]
	umaal r6, r8, r5, r2
	str r6, [r0, #48]
	ldr r5, [r4, #52]
	umaal r10, r8, r5, r2
	str r10, [r0, #52]
	add r0, r0, #56
	add r12, r12, #56
	add r4, r4, #56
	subs lr, lr, #14
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
261:
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 259b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
265:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 265b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
266:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 266b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
267:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 267b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 257b
	ldr r0, [r8, #136]
	ldr r4, [sp, #16]
	ldr r5, [sp, #20]
	ldr r6, [sp, #24]
	ldr r7, [sp, #28]
	ldr r8, [sp, #32]
	ldr r9, [sp, #36]
	ldr r10, [sp, #40]
	ldr r11, [sp, #44]
	ldr lr, [sp, #52]
	ldr r12, [sp], #56
	bx lr
