// The functions of `src/internal/vg_blake2b_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init_core:
	movw r12, #58983
	movt r12, #27145
	str r12, [r0, #4]
	movw r12, #42811
	movt r12, #33994
	str r12, [r0, #8]
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #12]
	movw r12, #63531
	movt r12, #65172
	str r12, [r0, #16]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #20]
	movw r12, #14065
	movt r12, #24349
	str r12, [r0, #24]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #28]
	movw r12, #33489
	movt r12, #44518
	str r12, [r0, #32]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #36]
	movw r12, #27679
	movt r12, #11070
	str r12, [r0, #40]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #44]
	movw r12, #48491
	movt r12, #64321
	str r12, [r0, #48]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #52]
	movw r12, #8569
	movt r12, #4990
	str r12, [r0, #56]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #60]
	movw r12, #51464
	movt r12, #62141
	eor r12, r12, r3, lsl #8
	eor r12, r12, r1
	str r12, [r0, #0]
	cmp r3, #0
	beq 20f
	mov r12, #0
	str r12, [r0, #64]
	str r12, [r0, #68]
	str r12, [r0, #72]
	str r12, [r0, #76]
	str r12, [r0, #80]
	str r12, [r0, #84]
	str r12, [r0, #88]
	str r12, [r0, #92]
	str r12, [r0, #96]
	str r12, [r0, #100]
	str r12, [r0, #104]
	str r12, [r0, #108]
	str r12, [r0, #112]
	str r12, [r0, #116]
	str r12, [r0, #120]
	str r12, [r0, #124]
	str r12, [r0, #128]
	str r12, [r0, #132]
	str r12, [r0, #136]
	str r12, [r0, #140]
	str r12, [r0, #144]
	str r12, [r0, #148]
	str r12, [r0, #152]
	str r12, [r0, #156]
	str r12, [r0, #160]
	str r12, [r0, #164]
	str r12, [r0, #168]
	str r12, [r0, #172]
	str r12, [r0, #176]
	str r12, [r0, #180]
	str r12, [r0, #184]
	str r12, [r0, #188]
	add r1, r0, #64
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
