// The functions of `src/internal/vg_seed_g8.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_g8:
	str lr, [r8, #220]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #128]
	ldr r10, [r8, #132]
	eor r0, r0, r10
	ldr r10, [r8, #140]
	eor r0, r0, r10
	ldr r1, [r8, #136]
	ldr r10, [r8, #140]
	eor r1, r1, r10
	ldr r10, [r8, #152]
	eor r1, r1, r10
	ldr r10, [r8, #156]
	eor r1, r1, r10
	ldr r2, [r8, #144]
	ldr r10, [r8, #148]
	eor r2, r2, r10
	ldr r10, [r8, #156]
	eor r2, r2, r10
	ldr r3, [r8, #132]
	ldr r10, [r8, #136]
	eor r3, r3, r10
	ldr r10, [r8, #140]
	eor r3, r3, r10
	ldr r10, [r8, #148]
	eor r3, r3, r10
	ldr r4, [r8, #132]
	ldr r10, [r8, #136]
	eor r4, r4, r10
	ldr r10, [r8, #144]
	eor r4, r4, r10
	ldr r5, [r8, #140]
	ldr r10, [r8, #144]
	eor r5, r5, r10
	ldr r6, [r8, #136]
	ldr r10, [r8, #140]
	eor r6, r6, r10
	ldr r10, [r8, #144]
	eor r6, r6, r10
	ldr r10, [r8, #148]
	eor r6, r6, r10
	ldr r7, [r8, #144]
	ldr r10, [r8, #148]
	eor r7, r7, r10
	ldr r10, [r8, #152]
	eor r7, r7, r10
	eor r2, r5, r2
	eor lr, r2, r1
	eor r10, lr, r6
	eor r3, r3, r10
	eor r3, r3, r7
	eor r12, r3, r2
	eor r11, r12, r4
	eor r0, lr, r0
	eor r1, r11, r1
	str r6, [r8, #0]
	eor r6, r0, r7
	str r11, [r8, #4]
	and r11, r6, r1
	eor r2, r11, r2
	eor r11, r3, r4
	str r6, [r8, #8]
	and r6, r7, lr
	str r1, [r8, #12]
	and r1, r0, r11
	str r11, [r8, #16]
	eor r11, r12, r0
	eor r4, r11, r4
	str r0, [r8, #20]
	and r0, r4, r11
	eor r5, r11, r5
	eor r2, r2, r0
	eor r3, r4, r3
	eor r0, r0, r6
	eor r6, r11, r10
	str r11, [r8, #24]
	eor r11, r5, r7
	eor r0, r0, r11
	str r7, [r8, #28]
	eor r7, r4, r11
	str r4, [r8, #32]
	and r4, r11, r10
	str r11, [r8, #36]
	ldr r11, [r8, #4]
	str r10, [r8, #40]
	and r10, r11, r3
	str r3, [r8, #44]
	and r3, r7, r6
	eor r4, r10, r4
	str r7, [r8, #48]
	eor r7, r11, r5
	eor r3, r10, r3
	ldr r10, [r8, #0]
	eor r0, r0, r10
	and r11, r5, r10
	eor r2, r2, r3
	eor r3, r1, r3
	eor r0, r0, r4
	eor r1, r5, r1
	eor r1, r1, lr
	eor r4, r1, r4
	and r1, r0, r2
	eor r4, r4, r11
	ldr r11, [r8, #12]
	eor r10, r6, r11
	and r11, r7, r10
	eor r3, r3, r11
	eor r11, r4, r1
	eor r3, r3, r12
	eor r12, r2, r3
	and r11, r11, r12
	eor r12, r3, r11
	eor r1, r3, r1
	eor r11, r1, r12
	and r3, r3, r11
	eor r2, r2, r3
	eor r0, r0, r4
	eor r2, r2, r12
	and r11, r0, r1
	eor r4, r4, r11
	eor r3, r1, r3
	and r3, r4, r3
	ldr r1, [r8, #40]
	and r1, r2, r1
	eor r0, r3, r0
	eor r3, r12, r2
	eor r11, r4, r0
	and lr, r12, lr
	and r5, r3, r5
	and r7, r11, r7
	and r11, r11, r10
	ldr r10, [r8, #0]
	and r3, r3, r10
	and r6, r0, r6
	eor r11, r11, r6
	eor r1, r1, lr
	eor r3, r3, lr
	eor lr, r4, r12
	ldr r10, [r8, #28]
	and r12, r12, r10
	eor r5, r12, r5
	eor r5, r5, r7
	ldr r10, [r8, #36]
	and r10, r2, r10
	eor r10, r10, r12
	ldr r12, [r8, #12]
	and r12, r4, r12
	eor r3, r3, r11
	eor r6, r12, r6
	ldr r12, [r8, #16]
	and r12, lr, r12
	eor r12, r12, r11
	eor r6, r6, r1
	ldr r11, [r8, #20]
	and r11, lr, r11
	eor r2, r0, r2
	eor lr, lr, r2
	eor r7, r7, r11
	eor r7, r7, r6
	ldr r11, [r8, #48]
	and r0, r0, r11
	ldr r11, [r8, #8]
	and r4, r4, r11
	eor r11, r0, r10
	ldr r10, [r8, #4]
	and r10, lr, r10
	eor r10, r10, r0
	ldr r0, [r8, #44]
	and lr, lr, r0
	eor r0, r7, r10
	ldr r7, [r8, #32]
	and r7, r2, r7
	eor r7, r10, r7
	ldr r10, [r8, #24]
	and r2, r2, r10
	eor r10, r2, r1
	eor r3, r3, lr
	eor r3, r3, r2
	eor r11, r4, r11
	eor r1, r7, r4
	eor r2, r5, r7
	eor r7, r1, lr
	eor r5, r6, r1
	eor r4, r11, r0
	eor r6, r12, r7
	eor r6, r6, r2
	eor r7, r10, r7
	mvn r0, r0
	mvn r1, r1
	mvn r5, r5
	mvn r6, r6
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	movw lr, #255
	movt lr, #255
	ldr r10, [r8, #132]
	and r11, r10, lr
	eor r0, r10, r11
	ldr r10, [r8, #136]
	and r10, r10, lr
	eor r0, r0, r10
	ldr r10, [r8, #140]
	eor r0, r0, r10
	and r10, r10, lr
	eor r0, r0, r10
	ldr r10, [r8, #144]
	and r10, r10, lr
	eor r0, r0, r10
	ldr r10, [r8, #148]
	and r10, r10, lr
	eor r0, r0, r10
	ldr r10, [r8, #152]
	and r10, r10, lr
	eor r0, r0, r10
	ldr r10, [r8, #132]
	and r11, r10, lr
	eor r1, r10, r11
	ldr r10, [r8, #136]
	and r10, r10, lr
	eor r1, r1, r10
	ldr r10, [r8, #144]
	eor r1, r1, r10
	ldr r10, [r8, #148]
	eor r1, r1, r10
	and r10, r10, lr
	eor r1, r1, r10
	ldr r10, [r8, #152]
	eor r1, r1, r10
	ldr r10, [r8, #156]
	eor r1, r1, r10
	ldr r2, [r8, #128]
	ldr r10, [r8, #132]
	and r10, r10, lr
	eor r2, r2, r10
	ldr r10, [r8, #136]
	eor r2, r2, r10
	and r10, r10, lr
	eor r2, r2, r10
	ldr r10, [r8, #140]
	eor r2, r2, r10
	and r10, r10, lr
	eor r2, r2, r10
	ldr r10, [r8, #144]
	eor r2, r2, r10
	ldr r10, [r8, #152]
	eor r2, r2, r10
	ldr r3, [r8, #128]
	ldr r10, [r8, #132]
	eor r3, r3, r10
	and r10, r10, lr
	eor r3, r3, r10
	ldr r10, [r8, #136]
	and r10, r10, lr
	eor r3, r3, r10
	ldr r10, [r8, #140]
	eor r3, r3, r10
	and r10, r10, lr
	eor r3, r3, r10
	ldr r10, [r8, #144]
	eor r3, r3, r10
	ldr r10, [r8, #148]
	eor r3, r3, r10
	ldr r10, [r8, #152]
	eor r3, r3, r10
	ldr r10, [r8, #156]
	and r10, r10, lr
	eor r3, r3, r10
	ldr r10, [r8, #128]
	and r4, r10, lr
	ldr r10, [r8, #136]
	and r10, r10, lr
	eor r4, r4, r10
	ldr r10, [r8, #140]
	eor r4, r4, r10
	ldr r10, [r8, #144]
	and r10, r10, lr
	eor r4, r4, r10
	ldr r10, [r8, #152]
	eor r4, r4, r10
	ldr r10, [r8, #156]
	eor r4, r4, r10
	and r10, r10, lr
	eor r4, r4, r10
	ldr r10, [r8, #128]
	and r5, r10, lr
	ldr r10, [r8, #132]
	and r10, r10, lr
	eor r5, r5, r10
	ldr r10, [r8, #140]
	eor r5, r5, r10
	ldr r10, [r8, #144]
	eor r5, r5, r10
	and r10, r10, lr
	eor r5, r5, r10
	ldr r10, [r8, #148]
	eor r5, r5, r10
	ldr r10, [r8, #152]
	eor r5, r5, r10
	ldr r10, [r8, #128]
	and r6, r10, lr
	ldr r10, [r8, #132]
	eor r6, r6, r10
	and r10, r10, lr
	eor r6, r6, r10
	ldr r10, [r8, #136]
	eor r6, r6, r10
	and r10, r10, lr
	eor r6, r6, r10
	ldr r10, [r8, #140]
	eor r6, r6, r10
	and r10, r10, lr
	eor r6, r6, r10
	ldr r10, [r8, #144]
	and r10, r10, lr
	eor r6, r6, r10
	ldr r10, [r8, #148]
	and r10, r10, lr
	eor r6, r6, r10
	ldr r10, [r8, #152]
	eor r6, r6, r10
	ldr r10, [r8, #132]
	and r7, r10, lr
	ldr r10, [r8, #140]
	eor r7, r7, r10
	ldr r10, [r8, #152]
	and r10, r10, lr
	eor r7, r7, r10
	ldr r10, [r8, #156]
	and r10, r10, lr
	eor r7, r7, r10
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r10, #53244
	movt r10, #53244
	str r10, [r8, #192]
	movw r10, #16371
	movt r10, #16371
	str r10, [r8, #196]
	movw r10, #64719
	movt r10, #64719
	str r10, [r8, #200]
	movw r10, #62271
	movt r10, #62271
	str r10, [r8, #204]
	movw r10, #59179
	movt r10, #59179
	str r10, [r8, #208]
	ldr r11, [r8, #192]
	and r11, r11, r0
	ldr r10, [r8, #196]
	and r10, r10, r0, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r0, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r0, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #192]
	and r11, r11, r1
	ldr r10, [r8, #196]
	and r10, r10, r1, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r1, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r1, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #192]
	and r11, r11, r2
	ldr r10, [r8, #196]
	and r10, r10, r2, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r2, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r2, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #192]
	and r11, r11, r3
	ldr r10, [r8, #196]
	and r10, r10, r3, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r3, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r3, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #192]
	and r11, r11, r4
	ldr r10, [r8, #196]
	and r10, r10, r4, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r4, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r4, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #192]
	and r11, r11, r5
	ldr r10, [r8, #196]
	and r10, r10, r5, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r5, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r5, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #192]
	and r11, r11, r6
	ldr r10, [r8, #196]
	and r10, r10, r6, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r6, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r6, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #192]
	and r11, r11, r7
	ldr r10, [r8, #196]
	and r10, r10, r7, ror #8
	eor r11, r11, r10
	ldr r10, [r8, #200]
	and r10, r10, r7, ror #16
	eor r11, r11, r10
	ldr r10, [r8, #204]
	and r10, r10, r7, ror #24
	eor r11, r11, r10
	ldr r10, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr lr, [r8, #220]
	bx lr
