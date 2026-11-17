// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	str r4, [r1, #396]
	str r5, [r1, #400]
	str r6, [r1, #404]
	str r7, [r1, #408]
	str r8, [r1, #412]
	str r9, [r1, #416]
	str r10, [r1, #420]
	str r11, [r1, #424]
	str lr, [r1, #428]
	movw r4, #65535
	movw r5, #255
	movt r5, #255
	movw r6, #3855
	movt r6, #3855
	movw r7, #13107
	movt r7, #13107
	movw r8, #21845
	movt r8, #21845
	ldr r2, [r0, #0]
	ldr r3, [r0, #4]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	str r2, [r1, #0]
	str r3, [r1, #4]
	ldr r2, [r0, #8]
	ldr r3, [r0, #12]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #22
	ror r3, r3, #22
	str r2, [r1, #8]
	str r3, [r1, #12]
	ldr r2, [r0, #16]
	ldr r3, [r0, #20]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #12
	ror r3, r3, #11
	str r2, [r1, #16]
	str r3, [r1, #20]
	ldr r2, [r0, #24]
	ldr r3, [r0, #28]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #16
	ror r3, r3, #15
	str r2, [r1, #24]
	str r3, [r1, #28]
	ldr r2, [r0, #32]
	ldr r3, [r0, #36]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #30
	ror r3, r3, #29
	str r2, [r1, #32]
	str r3, [r1, #36]
	ldr r2, [r0, #40]
	ldr r3, [r0, #44]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #19
	ror r3, r3, #19
	str r2, [r1, #40]
	str r3, [r1, #44]
	ldr r2, [r0, #48]
	ldr r3, [r0, #52]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #1
	str r2, [r1, #48]
	str r3, [r1, #52]
	ldr r2, [r0, #56]
	ldr r3, [r0, #60]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #3
	ror r3, r3, #2
	str r2, [r1, #56]
	str r3, [r1, #60]
	ldr r2, [r0, #64]
	ldr r3, [r0, #68]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #23
	ror r3, r3, #22
	str r2, [r1, #64]
	str r3, [r1, #68]
	ldr r2, [r0, #72]
	ldr r3, [r0, #76]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #21
	ror r3, r3, #20
	str r2, [r1, #72]
	str r3, [r1, #76]
	ldr r2, [r0, #80]
	ldr r3, [r0, #84]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #1
	str r2, [r1, #80]
	str r3, [r1, #84]
	ldr r2, [r0, #88]
	ldr r3, [r0, #92]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #25
	ror r3, r3, #25
	str r2, [r1, #88]
	str r3, [r1, #92]
	ldr r2, [r0, #96]
	ldr r3, [r0, #100]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #18
	ror r3, r3, #17
	str r2, [r1, #96]
	str r3, [r1, #100]
	ldr r2, [r0, #104]
	ldr r3, [r0, #108]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #27
	ror r3, r3, #26
	str r2, [r1, #104]
	str r3, [r1, #108]
	ldr r2, [r0, #112]
	ldr r3, [r0, #116]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #10
	ror r3, r3, #10
	str r2, [r1, #112]
	str r3, [r1, #116]
	ldr r2, [r0, #120]
	ldr r3, [r0, #124]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #4
	ror r3, r3, #4
	str r2, [r1, #120]
	str r3, [r1, #124]
	ldr r2, [r0, #128]
	ldr r3, [r0, #132]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #19
	ror r3, r3, #19
	str r2, [r1, #128]
	str r3, [r1, #132]
	ldr r2, [r0, #136]
	ldr r3, [r0, #140]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #5
	ror r3, r3, #5
	str r2, [r1, #136]
	str r3, [r1, #140]
	ldr r2, [r0, #144]
	ldr r3, [r0, #148]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #30
	ror r3, r3, #29
	str r2, [r1, #144]
	str r3, [r1, #148]
	ldr r2, [r0, #152]
	ldr r3, [r0, #156]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #1
	ror r3, r3, #1
	str r2, [r1, #152]
	str r3, [r1, #156]
	ldr r2, [r0, #160]
	ldr r3, [r0, #164]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #21
	ror r3, r3, #21
	str r2, [r1, #160]
	str r3, [r1, #164]
	ldr r2, [r0, #168]
	ldr r3, [r0, #172]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #1
	str r2, [r1, #168]
	str r3, [r1, #172]
	ldr r2, [r0, #176]
	ldr r3, [r0, #180]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #10
	ror r3, r3, #10
	str r2, [r1, #176]
	str r3, [r1, #180]
	ldr r2, [r0, #184]
	ldr r3, [r0, #188]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #22
	ror r3, r3, #21
	str r2, [r1, #184]
	str r3, [r1, #188]
	ldr r2, [r0, #192]
	ldr r3, [r0, #196]
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	ror r2, r2, #1
	ror r3, r3, #1
	str r2, [r1, #192]
	str r3, [r1, #196]
	movw r12, #1
	str r12, [r1, #200]
	movw r12, #0
	str r12, [r1, #204]
	movw r12, #0
	str r12, [r1, #208]
	movw r12, #137
	str r12, [r1, #212]
	movw r12, #0
	str r12, [r1, #216]
	movw r12, #139
	movt r12, #32768
	str r12, [r1, #220]
	movw r12, #0
	str r12, [r1, #224]
	movw r12, #32896
	movt r12, #32768
	str r12, [r1, #228]
	movw r12, #1
	str r12, [r1, #232]
	movw r12, #139
	str r12, [r1, #236]
	movw r12, #1
	str r12, [r1, #240]
	movw r12, #32768
	str r12, [r1, #244]
	movw r12, #1
	str r12, [r1, #248]
	movw r12, #32904
	movt r12, #32768
	str r12, [r1, #252]
	movw r12, #1
	str r12, [r1, #256]
	movw r12, #130
	movt r12, #32768
	str r12, [r1, #260]
	movw r12, #0
	str r12, [r1, #264]
	movw r12, #11
	str r12, [r1, #268]
	movw r12, #0
	str r12, [r1, #272]
	movw r12, #10
	str r12, [r1, #276]
	movw r12, #1
	str r12, [r1, #280]
	movw r12, #32898
	str r12, [r1, #284]
	movw r12, #0
	str r12, [r1, #288]
	movw r12, #32771
	str r12, [r1, #292]
	movw r12, #1
	str r12, [r1, #296]
	movw r12, #32907
	str r12, [r1, #300]
	movw r12, #1
	str r12, [r1, #304]
	movw r12, #11
	movt r12, #32768
	str r12, [r1, #308]
	movw r12, #1
	str r12, [r1, #312]
	movw r12, #138
	movt r12, #32768
	str r12, [r1, #316]
	movw r12, #1
	str r12, [r1, #320]
	movw r12, #129
	movt r12, #32768
	str r12, [r1, #324]
	movw r12, #0
	str r12, [r1, #328]
	movw r12, #129
	movt r12, #32768
	str r12, [r1, #332]
	movw r12, #0
	str r12, [r1, #336]
	movw r12, #8
	movt r12, #32768
	str r12, [r1, #340]
	movw r12, #0
	str r12, [r1, #344]
	movw r12, #131
	str r12, [r1, #348]
	movw r12, #0
	str r12, [r1, #352]
	movw r12, #32771
	movt r12, #32768
	str r12, [r1, #356]
	movw r12, #1
	str r12, [r1, #360]
	movw r12, #32904
	movt r12, #32768
	str r12, [r1, #364]
	movw r12, #0
	str r12, [r1, #368]
	movw r12, #136
	movt r12, #32768
	str r12, [r1, #372]
	movw r12, #1
	str r12, [r1, #376]
	movw r12, #32768
	str r12, [r1, #380]
	movw r12, #0
	str r12, [r1, #384]
	movw r12, #32898
	movt r12, #32768
	str r12, [r1, #388]
	add r12, r1, #200
	str r12, [r1, #392]
20:
	ldr r2, [r1, #0]
	ldr r12, [r1, #40]
	eor r2, r2, r12, ror #13
	ldr r12, [r1, #80]
	eor r2, r2, r12, ror #31
	ldr r12, [r1, #120]
	eor r2, r2, r12, ror #28
	ldr r12, [r1, #160]
	eor r2, r2, r12, ror #11
	ldr r3, [r1, #4]
	ldr r12, [r1, #44]
	eor r3, r3, r12, ror #13
	ldr r12, [r1, #84]
	eor r3, r3, r12
	ldr r12, [r1, #124]
	eor r3, r3, r12, ror #28
	ldr r12, [r1, #164]
	eor r3, r3, r12, ror #11
	ldr r4, [r1, #8]
	ldr r12, [r1, #48]
	eor r4, r4, r12, ror #21
	ldr r12, [r1, #88]
	eor r4, r4, r12, ror #29
	ldr r12, [r1, #128]
	eor r4, r4, r12, ror #3
	ldr r12, [r1, #168]
	eor r4, r4, r12, ror #21
	ldr r5, [r1, #12]
	ldr r12, [r1, #52]
	eor r5, r5, r12, ror #22
	ldr r12, [r1, #92]
	eor r5, r5, r12, ror #29
	ldr r12, [r1, #132]
	eor r5, r5, r12, ror #3
	ldr r12, [r1, #172]
	eor r5, r5, r12, ror #22
	ldr r6, [r1, #136]
	ldr r12, [r1, #16]
	eor r6, r6, r12, ror #25
	ldr r12, [r1, #56]
	eor r6, r6, r12, ror #2
	ldr r12, [r1, #96]
	eor r6, r6, r12, ror #19
	ldr r12, [r1, #176]
	eor r6, r6, r12, ror #27
	ldr r7, [r1, #140]
	ldr r12, [r1, #20]
	eor r7, r7, r12, ror #26
	ldr r12, [r1, #60]
	eor r7, r7, r12, ror #3
	ldr r12, [r1, #100]
	eor r7, r7, r12, ror #20
	ldr r12, [r1, #180]
	eor r7, r7, r12, ror #27
	ldr r8, [r1, #64]
	ldr r12, [r1, #24]
	eor r8, r8, r12, ror #7
	ldr r12, [r1, #104]
	eor r8, r8, r12, ror #28
	ldr r12, [r1, #144]
	eor r8, r8, r12, ror #25
	ldr r12, [r1, #184]
	eor r8, r8, r12, ror #1
	ldr r9, [r1, #68]
	ldr r12, [r1, #28]
	eor r9, r9, r12, ror #7
	ldr r12, [r1, #108]
	eor r9, r9, r12, ror #28
	ldr r12, [r1, #148]
	eor r9, r9, r12, ror #25
	ldr r12, [r1, #188]
	eor r9, r9, r12, ror #1
	ldr r10, [r1, #192]
	ldr r12, [r1, #32]
	eor r10, r10, r12, ror #3
	ldr r12, [r1, #72]
	eor r10, r10, r12, ror #12
	ldr r12, [r1, #112]
	eor r10, r10, r12, ror #23
	ldr r12, [r1, #152]
	eor r10, r10, r12
	ldr r11, [r1, #196]
	ldr r12, [r1, #36]
	eor r11, r11, r12, ror #4
	ldr r12, [r1, #76]
	eor r11, r11, r12, ror #13
	ldr r12, [r1, #116]
	eor r11, r11, r12, ror #23
	ldr r12, [r1, #156]
	eor r11, r11, r12
	eor r12, r10, r5, ror #10
	str r12, [r0, #164]
	eor r12, r11, r4, ror #11
	str r12, [r0, #172]
	eor r4, r4, r9, ror #31
	eor r5, r5, r8, ror #31
	eor r8, r8, r3, ror #22
	eor r9, r9, r2, ror #22
	eor r2, r2, r7, ror #26
	eor r3, r3, r6, ror #27
	eor r12, r6, r11, ror #3
	str r12, [r0, #180]
	eor r12, r7, r10, ror #4
	str r12, [r0, #188]
	ldr r6, [r1, #0]
	ldr r12, [r0, #164]
	eor r6, r6, r12, ror #31
	ldr r7, [r1, #48]
	eor r7, r2, r7, ror #31
	ldr r10, [r1, #100]
	eor r10, r5, r10, ror #5
	ldr r11, [r1, #148]
	ldr r12, [r0, #188]
	eor r11, r12, r11, ror #8
	ldr lr, [r1, #192]
	eor lr, r8, lr, ror #22
	bic r12, r10, r7, ror #22
	eor r12, r6, r12, ror #20
	str r12, [r0, #0]
	bic r12, r11, r10, ror #4
	eor r12, r7, r12, ror #6
	str r12, [r0, #8]
	bic r12, lr, r11, ror #14
	eor r12, r10, r12, ror #14
	str r12, [r0, #16]
	bic r12, r6, lr, ror #2
	eor r12, r11, r12, ror #16
	str r12, [r0, #24]
	bic r12, r7, r6, ror #22
	eor r12, lr, r12, ror #8
	str r12, [r0, #32]
	ldr r6, [r1, #4]
	ldr r12, [r0, #172]
	eor r6, r6, r12, ror #31
	ldr r7, [r1, #52]
	eor r7, r3, r7
	ldr r10, [r1, #96]
	eor r10, r4, r10, ror #4
	ldr r11, [r1, #144]
	ldr r12, [r0, #180]
	eor r11, r12, r11, ror #7
	ldr lr, [r1, #196]
	eor lr, r9, lr, ror #21
	bic r12, r10, r7, ror #21
	eor r12, r6, r12, ror #21
	str r12, [r0, #4]
	bic r12, r11, r10, ror #4
	eor r12, r7, r12, ror #7
	str r12, [r0, #12]
	bic r12, lr, r11, ror #14
	eor r12, r10, r12, ror #14
	str r12, [r0, #20]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #15
	str r12, [r0, #28]
	bic r12, r7, r6, ror #22
	eor r12, lr, r12, ror #7
	str r12, [r0, #36]
	ldr r6, [r1, #24]
	ldr r12, [r0, #180]
	eor r6, r12, r6, ror #21
	ldr r7, [r1, #72]
	eor r7, r8, r7, ror #2
	ldr r10, [r1, #84]
	ldr r12, [r0, #172]
	eor r10, r12, r10, ror #1
	ldr r11, [r1, #132]
	eor r11, r3, r11, ror #13
	ldr lr, [r1, #180]
	eor lr, r5, lr, ror #12
	bic r12, r10, r7, ror #2
	eor r12, r6, r12, ror #16
	str r12, [r0, #40]
	bic r12, r11, r10, ror #20
	eor r12, r7, r12, ror #10
	str r12, [r0, #48]
	bic r12, lr, r11, ror #30
	eor r12, r10, r12, ror #14
	str r12, [r0, #56]
	bic r12, r6, lr, ror #30
	eor r12, r11, r12, ror #4
	str r12, [r0, #64]
	bic r12, r7, r6, ror #14
	eor r12, lr, r12, ror #20
	str r12, [r0, #72]
	ldr r6, [r1, #28]
	ldr r12, [r0, #188]
	eor r6, r12, r6, ror #22
	ldr r7, [r1, #76]
	eor r7, r9, r7, ror #2
	ldr r10, [r1, #80]
	ldr r12, [r0, #164]
	eor r10, r12, r10
	ldr r11, [r1, #128]
	eor r11, r2, r11, ror #13
	ldr lr, [r1, #176]
	eor lr, r4, lr, ror #12
	bic r12, r10, r7, ror #2
	eor r12, r6, r12, ror #17
	str r12, [r0, #44]
	bic r12, r11, r10, ror #20
	eor r12, r7, r12, ror #10
	str r12, [r0, #52]
	bic r12, lr, r11, ror #30
	eor r12, r10, r12, ror #14
	str r12, [r0, #60]
	bic r12, r6, lr, ror #31
	eor r12, r11, r12, ror #3
	str r12, [r0, #68]
	bic r12, r7, r6, ror #13
	eor r12, lr, r12, ror #20
	str r12, [r0, #76]
	ldr r6, [r1, #12]
	eor r6, r3, r6, ror #10
	ldr r7, [r1, #56]
	eor r7, r4, r7, ror #19
	ldr r10, [r1, #108]
	ldr r12, [r0, #188]
	eor r10, r12, r10, ror #11
	ldr r11, [r1, #152]
	eor r11, r8, r11, ror #22
	ldr lr, [r1, #160]
	ldr r12, [r0, #164]
	eor lr, r12, lr, ror #12
	bic r12, r10, r7, ror #25
	eor r12, r6, r12, ror #15
	str r12, [r0, #80]
	bic r12, r11, r10, ror #9
	eor r12, r7, r12, ror #30
	str r12, [r0, #88]
	bic r12, lr, r11, ror #15
	eor r12, r10, r12, ror #8
	str r12, [r0, #96]
	bic r12, r6, lr, ror #23
	eor r12, r11, r12, ror #26
	str r12, [r0, #104]
	bic r12, r7, r6, ror #24
	eor r12, lr, r12, ror #17
	str r12, [r0, #112]
	ldr r6, [r1, #8]
	eor r6, r2, r6, ror #10
	ldr r7, [r1, #60]
	eor r7, r5, r7, ror #20
	ldr r10, [r1, #104]
	ldr r12, [r0, #180]
	eor r10, r12, r10, ror #10
	ldr r11, [r1, #156]
	eor r11, r9, r11, ror #21
	ldr lr, [r1, #164]
	ldr r12, [r0, #172]
	eor lr, r12, lr, ror #12
	bic r12, r10, r7, ror #24
	eor r12, r6, r12, ror #15
	str r12, [r0, #84]
	bic r12, r11, r10, ror #9
	eor r12, r7, r12, ror #31
	str r12, [r0, #92]
	bic r12, lr, r11, ror #16
	eor r12, r10, r12, ror #7
	str r12, [r0, #100]
	bic r12, r6, lr, ror #22
	eor r12, r11, r12, ror #26
	str r12, [r0, #108]
	bic r12, r7, r6, ror #25
	eor r12, lr, r12, ror #17
	str r12, [r0, #116]
	ldr r6, [r1, #36]
	eor r6, r9, r6, ror #25
	ldr r7, [r1, #40]
	ldr r12, [r0, #164]
	eor r7, r12, r7, ror #14
	ldr r10, [r1, #88]
	eor r10, r2, r10, ror #7
	ldr r11, [r1, #140]
	eor r11, r5, r11, ror #17
	ldr lr, [r1, #184]
	ldr r12, [r0, #180]
	eor lr, r12, lr, ror #15
	bic r12, r10, r7, ror #18
	eor r12, r6, r12, ror #31
	str r12, [r0, #120]
	bic r12, r11, r10, ror #25
	eor r12, r7, r12, ror #21
	str r12, [r0, #128]
	bic r12, lr, r11, ror #3
	eor r12, r10, r12, ror #4
	str r12, [r0, #136]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #26
	str r12, [r0, #144]
	bic r12, r7, r6, ror #15
	eor r12, lr, r12, ror #14
	str r12, [r0, #152]
	ldr r6, [r1, #32]
	eor r6, r8, r6, ror #25
	ldr r7, [r1, #44]
	ldr r12, [r0, #172]
	eor r7, r12, r7, ror #14
	ldr r10, [r1, #92]
	eor r10, r3, r10, ror #7
	ldr r11, [r1, #136]
	eor r11, r4, r11, ror #17
	ldr lr, [r1, #188]
	ldr r12, [r0, #188]
	eor lr, r12, lr, ror #16
	bic r12, r10, r7, ror #18
	eor r12, r6, r12, ror #31
	str r12, [r0, #124]
	bic r12, r11, r10, ror #24
	eor r12, r7, r12, ror #22
	str r12, [r0, #132]
	bic r12, lr, r11, ror #4
	eor r12, r10, r12, ror #4
	str r12, [r0, #140]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #25
	str r12, [r0, #148]
	bic r12, r7, r6, ror #15
	eor r12, lr, r12, ror #14
	str r12, [r0, #156]
	ldr r6, [r1, #16]
	eor r6, r4, r6, ror #10
	ldr r7, [r1, #68]
	ldr r12, [r0, #188]
	eor r7, r12, r7, ror #15
	ldr r10, [r1, #116]
	eor r10, r9, r10, ror #12
	ldr r11, [r1, #124]
	ldr r12, [r0, #172]
	eor r11, r12, r11, ror #29
	ldr lr, [r1, #168]
	eor lr, r2, lr, ror #31
	bic r12, r10, r7, ror #9
	eor r12, r6, r12, ror #11
	str r12, [r0, #160]
	bic r12, r11, r10, ror #12
	eor r12, r7, r12, ror #11
	str r12, [r0, #168]
	bic r12, lr, r11, ror #11
	eor r12, r10, r12, ror #9
	str r12, [r0, #176]
	bic r12, r6, lr, ror #20
	eor r12, r11, r12, ror #1
	str r12, [r0, #184]
	bic r12, r7, r6, ror #12
	eor r12, lr, r12
	str r12, [r0, #192]
	ldr r6, [r1, #20]
	eor r6, r5, r6, ror #11
	ldr r7, [r1, #64]
	ldr r12, [r0, #180]
	eor r7, r12, r7, ror #14
	ldr r10, [r1, #112]
	eor r10, r8, r10, ror #13
	ldr r11, [r1, #120]
	ldr r12, [r0, #164]
	eor r11, r12, r11, ror #29
	ldr lr, [r1, #172]
	eor lr, r3, lr
	bic r12, r10, r7, ror #10
	eor r12, r6, r12, ror #11
	str r12, [r0, #164]
	bic r12, r11, r10, ror #11
	eor r12, r7, r12, ror #11
	str r12, [r0, #172]
	bic r12, lr, r11, ror #12
	eor r12, r10, r12, ror #9
	str r12, [r0, #180]
	bic r12, r6, lr, ror #20
	eor r12, r11, r12
	str r12, [r0, #188]
	bic r12, r7, r6, ror #11
	eor r12, lr, r12, ror #1
	str r12, [r0, #196]
	ldr r12, [r1, #392]
	ldr lr, [r0, #0]
	ldr r6, [r12, #0]
	eor lr, lr, r6
	str lr, [r0, #0]
	ldr lr, [r0, #4]
	ldr r6, [r12, #4]
	eor lr, lr, r6
	str lr, [r0, #4]
	add r12, r12, #8
	str r12, [r1, #392]
	ldr r2, [r0, #0]
	ldr r12, [r0, #40]
	eor r2, r2, r12, ror #13
	ldr r12, [r0, #80]
	eor r2, r2, r12, ror #31
	ldr r12, [r0, #120]
	eor r2, r2, r12, ror #28
	ldr r12, [r0, #160]
	eor r2, r2, r12, ror #11
	ldr r3, [r0, #4]
	ldr r12, [r0, #44]
	eor r3, r3, r12, ror #13
	ldr r12, [r0, #84]
	eor r3, r3, r12
	ldr r12, [r0, #124]
	eor r3, r3, r12, ror #28
	ldr r12, [r0, #164]
	eor r3, r3, r12, ror #11
	ldr r4, [r0, #8]
	ldr r12, [r0, #48]
	eor r4, r4, r12, ror #21
	ldr r12, [r0, #88]
	eor r4, r4, r12, ror #29
	ldr r12, [r0, #128]
	eor r4, r4, r12, ror #3
	ldr r12, [r0, #168]
	eor r4, r4, r12, ror #21
	ldr r5, [r0, #12]
	ldr r12, [r0, #52]
	eor r5, r5, r12, ror #22
	ldr r12, [r0, #92]
	eor r5, r5, r12, ror #29
	ldr r12, [r0, #132]
	eor r5, r5, r12, ror #3
	ldr r12, [r0, #172]
	eor r5, r5, r12, ror #22
	ldr r6, [r0, #136]
	ldr r12, [r0, #16]
	eor r6, r6, r12, ror #25
	ldr r12, [r0, #56]
	eor r6, r6, r12, ror #2
	ldr r12, [r0, #96]
	eor r6, r6, r12, ror #19
	ldr r12, [r0, #176]
	eor r6, r6, r12, ror #27
	ldr r7, [r0, #140]
	ldr r12, [r0, #20]
	eor r7, r7, r12, ror #26
	ldr r12, [r0, #60]
	eor r7, r7, r12, ror #3
	ldr r12, [r0, #100]
	eor r7, r7, r12, ror #20
	ldr r12, [r0, #180]
	eor r7, r7, r12, ror #27
	ldr r8, [r0, #64]
	ldr r12, [r0, #24]
	eor r8, r8, r12, ror #7
	ldr r12, [r0, #104]
	eor r8, r8, r12, ror #28
	ldr r12, [r0, #144]
	eor r8, r8, r12, ror #25
	ldr r12, [r0, #184]
	eor r8, r8, r12, ror #1
	ldr r9, [r0, #68]
	ldr r12, [r0, #28]
	eor r9, r9, r12, ror #7
	ldr r12, [r0, #108]
	eor r9, r9, r12, ror #28
	ldr r12, [r0, #148]
	eor r9, r9, r12, ror #25
	ldr r12, [r0, #188]
	eor r9, r9, r12, ror #1
	ldr r10, [r0, #192]
	ldr r12, [r0, #32]
	eor r10, r10, r12, ror #3
	ldr r12, [r0, #72]
	eor r10, r10, r12, ror #12
	ldr r12, [r0, #112]
	eor r10, r10, r12, ror #23
	ldr r12, [r0, #152]
	eor r10, r10, r12
	ldr r11, [r0, #196]
	ldr r12, [r0, #36]
	eor r11, r11, r12, ror #4
	ldr r12, [r0, #76]
	eor r11, r11, r12, ror #13
	ldr r12, [r0, #116]
	eor r11, r11, r12, ror #23
	ldr r12, [r0, #156]
	eor r11, r11, r12
	eor r12, r10, r5, ror #10
	str r12, [r1, #164]
	eor r12, r11, r4, ror #11
	str r12, [r1, #172]
	eor r4, r4, r9, ror #31
	eor r5, r5, r8, ror #31
	eor r8, r8, r3, ror #22
	eor r9, r9, r2, ror #22
	eor r2, r2, r7, ror #26
	eor r3, r3, r6, ror #27
	eor r12, r6, r11, ror #3
	str r12, [r1, #180]
	eor r12, r7, r10, ror #4
	str r12, [r1, #188]
	ldr r6, [r0, #0]
	ldr r12, [r1, #164]
	eor r6, r6, r12, ror #31
	ldr r7, [r0, #48]
	eor r7, r2, r7, ror #31
	ldr r10, [r0, #100]
	eor r10, r5, r10, ror #5
	ldr r11, [r0, #148]
	ldr r12, [r1, #188]
	eor r11, r12, r11, ror #8
	ldr lr, [r0, #192]
	eor lr, r8, lr, ror #22
	bic r12, r10, r7, ror #22
	eor r12, r6, r12, ror #20
	str r12, [r1, #0]
	bic r12, r11, r10, ror #4
	eor r12, r7, r12, ror #6
	str r12, [r1, #8]
	bic r12, lr, r11, ror #14
	eor r12, r10, r12, ror #14
	str r12, [r1, #16]
	bic r12, r6, lr, ror #2
	eor r12, r11, r12, ror #16
	str r12, [r1, #24]
	bic r12, r7, r6, ror #22
	eor r12, lr, r12, ror #8
	str r12, [r1, #32]
	ldr r6, [r0, #4]
	ldr r12, [r1, #172]
	eor r6, r6, r12, ror #31
	ldr r7, [r0, #52]
	eor r7, r3, r7
	ldr r10, [r0, #96]
	eor r10, r4, r10, ror #4
	ldr r11, [r0, #144]
	ldr r12, [r1, #180]
	eor r11, r12, r11, ror #7
	ldr lr, [r0, #196]
	eor lr, r9, lr, ror #21
	bic r12, r10, r7, ror #21
	eor r12, r6, r12, ror #21
	str r12, [r1, #4]
	bic r12, r11, r10, ror #4
	eor r12, r7, r12, ror #7
	str r12, [r1, #12]
	bic r12, lr, r11, ror #14
	eor r12, r10, r12, ror #14
	str r12, [r1, #20]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #15
	str r12, [r1, #28]
	bic r12, r7, r6, ror #22
	eor r12, lr, r12, ror #7
	str r12, [r1, #36]
	ldr r6, [r0, #24]
	ldr r12, [r1, #180]
	eor r6, r12, r6, ror #21
	ldr r7, [r0, #72]
	eor r7, r8, r7, ror #2
	ldr r10, [r0, #84]
	ldr r12, [r1, #172]
	eor r10, r12, r10, ror #1
	ldr r11, [r0, #132]
	eor r11, r3, r11, ror #13
	ldr lr, [r0, #180]
	eor lr, r5, lr, ror #12
	bic r12, r10, r7, ror #2
	eor r12, r6, r12, ror #16
	str r12, [r1, #40]
	bic r12, r11, r10, ror #20
	eor r12, r7, r12, ror #10
	str r12, [r1, #48]
	bic r12, lr, r11, ror #30
	eor r12, r10, r12, ror #14
	str r12, [r1, #56]
	bic r12, r6, lr, ror #30
	eor r12, r11, r12, ror #4
	str r12, [r1, #64]
	bic r12, r7, r6, ror #14
	eor r12, lr, r12, ror #20
	str r12, [r1, #72]
	ldr r6, [r0, #28]
	ldr r12, [r1, #188]
	eor r6, r12, r6, ror #22
	ldr r7, [r0, #76]
	eor r7, r9, r7, ror #2
	ldr r10, [r0, #80]
	ldr r12, [r1, #164]
	eor r10, r12, r10
	ldr r11, [r0, #128]
	eor r11, r2, r11, ror #13
	ldr lr, [r0, #176]
	eor lr, r4, lr, ror #12
	bic r12, r10, r7, ror #2
	eor r12, r6, r12, ror #17
	str r12, [r1, #44]
	bic r12, r11, r10, ror #20
	eor r12, r7, r12, ror #10
	str r12, [r1, #52]
	bic r12, lr, r11, ror #30
	eor r12, r10, r12, ror #14
	str r12, [r1, #60]
	bic r12, r6, lr, ror #31
	eor r12, r11, r12, ror #3
	str r12, [r1, #68]
	bic r12, r7, r6, ror #13
	eor r12, lr, r12, ror #20
	str r12, [r1, #76]
	ldr r6, [r0, #12]
	eor r6, r3, r6, ror #10
	ldr r7, [r0, #56]
	eor r7, r4, r7, ror #19
	ldr r10, [r0, #108]
	ldr r12, [r1, #188]
	eor r10, r12, r10, ror #11
	ldr r11, [r0, #152]
	eor r11, r8, r11, ror #22
	ldr lr, [r0, #160]
	ldr r12, [r1, #164]
	eor lr, r12, lr, ror #12
	bic r12, r10, r7, ror #25
	eor r12, r6, r12, ror #15
	str r12, [r1, #80]
	bic r12, r11, r10, ror #9
	eor r12, r7, r12, ror #30
	str r12, [r1, #88]
	bic r12, lr, r11, ror #15
	eor r12, r10, r12, ror #8
	str r12, [r1, #96]
	bic r12, r6, lr, ror #23
	eor r12, r11, r12, ror #26
	str r12, [r1, #104]
	bic r12, r7, r6, ror #24
	eor r12, lr, r12, ror #17
	str r12, [r1, #112]
	ldr r6, [r0, #8]
	eor r6, r2, r6, ror #10
	ldr r7, [r0, #60]
	eor r7, r5, r7, ror #20
	ldr r10, [r0, #104]
	ldr r12, [r1, #180]
	eor r10, r12, r10, ror #10
	ldr r11, [r0, #156]
	eor r11, r9, r11, ror #21
	ldr lr, [r0, #164]
	ldr r12, [r1, #172]
	eor lr, r12, lr, ror #12
	bic r12, r10, r7, ror #24
	eor r12, r6, r12, ror #15
	str r12, [r1, #84]
	bic r12, r11, r10, ror #9
	eor r12, r7, r12, ror #31
	str r12, [r1, #92]
	bic r12, lr, r11, ror #16
	eor r12, r10, r12, ror #7
	str r12, [r1, #100]
	bic r12, r6, lr, ror #22
	eor r12, r11, r12, ror #26
	str r12, [r1, #108]
	bic r12, r7, r6, ror #25
	eor r12, lr, r12, ror #17
	str r12, [r1, #116]
	ldr r6, [r0, #36]
	eor r6, r9, r6, ror #25
	ldr r7, [r0, #40]
	ldr r12, [r1, #164]
	eor r7, r12, r7, ror #14
	ldr r10, [r0, #88]
	eor r10, r2, r10, ror #7
	ldr r11, [r0, #140]
	eor r11, r5, r11, ror #17
	ldr lr, [r0, #184]
	ldr r12, [r1, #180]
	eor lr, r12, lr, ror #15
	bic r12, r10, r7, ror #18
	eor r12, r6, r12, ror #31
	str r12, [r1, #120]
	bic r12, r11, r10, ror #25
	eor r12, r7, r12, ror #21
	str r12, [r1, #128]
	bic r12, lr, r11, ror #3
	eor r12, r10, r12, ror #4
	str r12, [r1, #136]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #26
	str r12, [r1, #144]
	bic r12, r7, r6, ror #15
	eor r12, lr, r12, ror #14
	str r12, [r1, #152]
	ldr r6, [r0, #32]
	eor r6, r8, r6, ror #25
	ldr r7, [r0, #44]
	ldr r12, [r1, #172]
	eor r7, r12, r7, ror #14
	ldr r10, [r0, #92]
	eor r10, r3, r10, ror #7
	ldr r11, [r0, #136]
	eor r11, r4, r11, ror #17
	ldr lr, [r0, #188]
	ldr r12, [r1, #188]
	eor lr, r12, lr, ror #16
	bic r12, r10, r7, ror #18
	eor r12, r6, r12, ror #31
	str r12, [r1, #124]
	bic r12, r11, r10, ror #24
	eor r12, r7, r12, ror #22
	str r12, [r1, #132]
	bic r12, lr, r11, ror #4
	eor r12, r10, r12, ror #4
	str r12, [r1, #140]
	bic r12, r6, lr, ror #3
	eor r12, r11, r12, ror #25
	str r12, [r1, #148]
	bic r12, r7, r6, ror #15
	eor r12, lr, r12, ror #14
	str r12, [r1, #156]
	ldr r6, [r0, #16]
	eor r6, r4, r6, ror #10
	ldr r7, [r0, #68]
	ldr r12, [r1, #188]
	eor r7, r12, r7, ror #15
	ldr r10, [r0, #116]
	eor r10, r9, r10, ror #12
	ldr r11, [r0, #124]
	ldr r12, [r1, #172]
	eor r11, r12, r11, ror #29
	ldr lr, [r0, #168]
	eor lr, r2, lr, ror #31
	bic r12, r10, r7, ror #9
	eor r12, r6, r12, ror #11
	str r12, [r1, #160]
	bic r12, r11, r10, ror #12
	eor r12, r7, r12, ror #11
	str r12, [r1, #168]
	bic r12, lr, r11, ror #11
	eor r12, r10, r12, ror #9
	str r12, [r1, #176]
	bic r12, r6, lr, ror #20
	eor r12, r11, r12, ror #1
	str r12, [r1, #184]
	bic r12, r7, r6, ror #12
	eor r12, lr, r12
	str r12, [r1, #192]
	ldr r6, [r0, #20]
	eor r6, r5, r6, ror #11
	ldr r7, [r0, #64]
	ldr r12, [r1, #180]
	eor r7, r12, r7, ror #14
	ldr r10, [r0, #112]
	eor r10, r8, r10, ror #13
	ldr r11, [r0, #120]
	ldr r12, [r1, #164]
	eor r11, r12, r11, ror #29
	ldr lr, [r0, #172]
	eor lr, r3, lr
	bic r12, r10, r7, ror #10
	eor r12, r6, r12, ror #11
	str r12, [r1, #164]
	bic r12, r11, r10, ror #11
	eor r12, r7, r12, ror #11
	str r12, [r1, #172]
	bic r12, lr, r11, ror #12
	eor r12, r10, r12, ror #9
	str r12, [r1, #180]
	bic r12, r6, lr, ror #20
	eor r12, r11, r12
	str r12, [r1, #188]
	bic r12, r7, r6, ror #11
	eor r12, lr, r12, ror #1
	str r12, [r1, #196]
	ldr r12, [r1, #392]
	ldr lr, [r1, #0]
	ldr r6, [r12, #0]
	eor lr, lr, r6
	str lr, [r1, #0]
	ldr lr, [r1, #4]
	ldr r6, [r12, #4]
	eor lr, lr, r6
	str lr, [r1, #4]
	add r12, r12, #8
	str r12, [r1, #392]
	ldr r12, [r1, #392]
	sub r12, r12, r1
	cmp r12, #392
	bne 20b
	movw r4, #65535
	movw r5, #255
	movt r5, #255
	movw r6, #3855
	movt r6, #3855
	movw r7, #13107
	movt r7, #13107
	movw r8, #21845
	movt r8, #21845
	ldr r2, [r1, #0]
	ldr r3, [r1, #4]
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #0]
	str r3, [r0, #4]
	ldr r2, [r1, #8]
	ldr r3, [r1, #12]
	ror r2, r2, #10
	ror r3, r3, #10
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #8]
	str r3, [r0, #12]
	ldr r2, [r1, #16]
	ldr r3, [r1, #20]
	ror r2, r2, #20
	ror r3, r3, #21
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #16]
	str r3, [r0, #20]
	ldr r2, [r1, #24]
	ldr r3, [r1, #28]
	ror r2, r2, #16
	ror r3, r3, #17
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #24]
	str r3, [r0, #28]
	ldr r2, [r1, #32]
	ldr r3, [r1, #36]
	ror r2, r2, #2
	ror r3, r3, #3
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #32]
	str r3, [r0, #36]
	ldr r2, [r1, #40]
	ldr r3, [r1, #44]
	ror r2, r2, #13
	ror r3, r3, #13
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #40]
	str r3, [r0, #44]
	ldr r2, [r1, #48]
	ldr r3, [r1, #52]
	ror r2, r2, #31
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #48]
	str r3, [r0, #52]
	ldr r2, [r1, #56]
	ldr r3, [r1, #60]
	ror r2, r2, #29
	ror r3, r3, #30
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #56]
	str r3, [r0, #60]
	ldr r2, [r1, #64]
	ldr r3, [r1, #68]
	ror r2, r2, #9
	ror r3, r3, #10
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #64]
	str r3, [r0, #68]
	ldr r2, [r1, #72]
	ldr r3, [r1, #76]
	ror r2, r2, #11
	ror r3, r3, #12
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #72]
	str r3, [r0, #76]
	ldr r2, [r1, #80]
	ldr r3, [r1, #84]
	ror r2, r2, #31
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #80]
	str r3, [r0, #84]
	ldr r2, [r1, #88]
	ldr r3, [r1, #92]
	ror r2, r2, #7
	ror r3, r3, #7
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #88]
	str r3, [r0, #92]
	ldr r2, [r1, #96]
	ldr r3, [r1, #100]
	ror r2, r2, #14
	ror r3, r3, #15
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #96]
	str r3, [r0, #100]
	ldr r2, [r1, #104]
	ldr r3, [r1, #108]
	ror r2, r2, #5
	ror r3, r3, #6
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #104]
	str r3, [r0, #108]
	ldr r2, [r1, #112]
	ldr r3, [r1, #116]
	ror r2, r2, #22
	ror r3, r3, #22
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #112]
	str r3, [r0, #116]
	ldr r2, [r1, #120]
	ldr r3, [r1, #124]
	ror r2, r2, #28
	ror r3, r3, #28
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #120]
	str r3, [r0, #124]
	ldr r2, [r1, #128]
	ldr r3, [r1, #132]
	ror r2, r2, #13
	ror r3, r3, #13
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #128]
	str r3, [r0, #132]
	ldr r2, [r1, #136]
	ldr r3, [r1, #140]
	ror r2, r2, #27
	ror r3, r3, #27
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #136]
	str r3, [r0, #140]
	ldr r2, [r1, #144]
	ldr r3, [r1, #148]
	ror r2, r2, #2
	ror r3, r3, #3
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #144]
	str r3, [r0, #148]
	ldr r2, [r1, #152]
	ldr r3, [r1, #156]
	ror r2, r2, #31
	ror r3, r3, #31
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #152]
	str r3, [r0, #156]
	ldr r2, [r1, #160]
	ldr r3, [r1, #164]
	ror r2, r2, #11
	ror r3, r3, #11
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #160]
	str r3, [r0, #164]
	ldr r2, [r1, #168]
	ldr r3, [r1, #172]
	ror r2, r2, #31
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #168]
	str r3, [r0, #172]
	ldr r2, [r1, #176]
	ldr r3, [r1, #180]
	ror r2, r2, #22
	ror r3, r3, #22
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #176]
	str r3, [r0, #180]
	ldr r2, [r1, #184]
	ldr r3, [r1, #188]
	ror r2, r2, #10
	ror r3, r3, #11
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #184]
	str r3, [r0, #188]
	ldr r2, [r1, #192]
	ldr r3, [r1, #196]
	ror r2, r2, #31
	ror r3, r3, #31
	eor r12, r3, r2, lsr #1
	and r12, r12, r8
	eor r3, r3, r12
	eor r2, r2, r12, ror #31
	eor r12, r3, r2, lsr #2
	and r12, r12, r7
	eor r3, r3, r12
	eor r2, r2, r12, ror #30
	eor r12, r3, r2, lsr #4
	and r12, r12, r6
	eor r3, r3, r12
	eor r2, r2, r12, ror #28
	eor r12, r3, r2, lsr #8
	and r12, r12, r5
	eor r3, r3, r12
	eor r2, r2, r12, ror #24
	eor r12, r3, r2, lsr #16
	and r12, r12, r4
	eor r3, r3, r12
	eor r2, r2, r12, ror #16
	str r2, [r0, #192]
	str r3, [r0, #196]
	ldr r4, [r1, #396]
	ldr r5, [r1, #400]
	ldr r6, [r1, #404]
	ldr r7, [r1, #408]
	ldr r8, [r1, #412]
	ldr r9, [r1, #416]
	ldr r10, [r1, #420]
	ldr r11, [r1, #424]
	ldr lr, [r1, #428]
	bx lr
