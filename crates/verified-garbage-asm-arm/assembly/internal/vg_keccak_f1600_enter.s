// The functions of `src/internal/vg_keccak_f1600_enter.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_enter:
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
	bx lr
