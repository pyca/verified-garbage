// The functions of `src/ed25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	add x19, x0, #0
	add x0, x4, #0
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x3, #0]
	ldr x5, [x3, #8]
	ldr x6, [x3, #16]
	ldr x7, [x3, #24]
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	ldr x4, [x1, #0]
	ldr x5, [x1, #8]
	ldr x6, [x1, #16]
	ldr x7, [x1, #24]
	movz w10, #0, lsl #0
	ldr x3, [x0, #64]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x4, x4, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x5, x5, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x21, x20, #0
	ldr x3, [x0, #72]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x5, x5, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x22, x20, #0
	ldr x3, [x0, #80]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x22, x22, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x23, x20, #0
	ldr x3, [x0, #88]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x22, x22, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x23, x23, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x24, x20, #0
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	str x21, [x0, #160]
	str x22, [x0, #168]
	str x23, [x0, #176]
	str x24, [x0, #184]
	add x1, x0, #128
	add x2, x0, #0
	add x0, x19, #0
	movz w4, #0, lsl #0
	movz w5, #0, lsl #0
	movz w6, #0, lsl #0
	movz w7, #0, lsl #0
	movz w10, #0, lsl #0
	movz w19, #64, lsl #0
20:
	sub x19, x19, #8
	add x9, x1, x19
	ldr x3, [x9, #0]
	lsr x12, x6, #60
	lsl x13, x7, #4
	orr x12, x12, x13
	lsr x13, x7, #60
	lsl x7, x6, #4
	lsr x7, x7, #4
	add x6, x5, #0
	add x5, x4, #0
	add x4, x3, #0
	movz x8, #54253, lsl #0
	movk x8, #23797, lsl #16
	movk x8, #25370, lsl #32
	movk x8, #22546, lsl #48
	movz x17, #40150, lsl #0
	movk x17, #41719, lsl #16
	movk x17, #63966, lsl #32
	movk x17, #5342, lsl #48
	mul x14, x12, x8
	umulh x15, x12, x8
	mul x9, x12, x17
	umulh x16, x12, x17
	adds x15, x15, x9
	adcs x16, x16, x10
	mul x9, x13, x8
	mul x13, x13, x17
	adds x15, x15, x9
	adcs x16, x16, x13
	subs x14, x8, x14
	sbcs x15, x17, x15
	sbcs x16, x10, x16
	movz x9, #4096, lsl #48
	sbcs x9, x9, x10
	adds x4, x4, x14
	adcs x5, x5, x15
	adcs x6, x6, x16
	adcs x7, x7, x9
	add x21, x4, #0
	add x22, x5, #0
	add x23, x6, #0
	add x24, x7, #0
	movz x3, #54253, lsl #0
	movk x3, #23797, lsl #16
	movk x3, #25370, lsl #32
	movk x3, #22546, lsl #48
	subs x4, x4, x3
	movz x3, #40150, lsl #0
	movk x3, #41719, lsl #16
	movk x3, #63966, lsl #32
	movk x3, #5342, lsl #48
	sbcs x5, x5, x3
	sbcs x6, x6, x10
	movz x3, #0, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #4096, lsl #48
	sbcs x7, x7, x3
	sbcs x8, x10, x10
	eor x21, x21, x4
	and x21, x21, x8
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x8
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x8
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x8
	eor x7, x7, x24
	cbnz x19, 20b
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	ret
	.p2align 6

vg_ed25519_public_key_expanded:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x1, [sp, #264]
	add x1, x1, #0
	add x15, sp, #192
	ldr x9, [x1, #0]
	str x9, [x15, #0]
	ldr x9, [x1, #8]
	str x9, [x15, #8]
	ldr x9, [x1, #16]
	str x9, [x15, #16]
	ldr x9, [x1, #24]
	str x9, [x15, #24]
	ldr x9, [x1, #32]
	str x9, [x15, #32]
	ldr x9, [x1, #40]
	str x9, [x15, #40]
	ldr x9, [x1, #48]
	str x9, [x15, #48]
	ldr x9, [x1, #56]
	str x9, [x15, #56]
	ldr x9, [sp, #192]
	movz x10, #65528, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #200]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #208]
	add x15, sp, #48
	str x9, [x15, #0]
	ldr x9, [sp, #216]
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #16383, lsl #48
	and x9, x9, x10
	movz x10, #16384, lsl #48
	orr x9, x9, x10
	add x15, sp, #56
	str x9, [x15, #0]
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #32
	ldr x2, [sp, #272]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #32]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #40]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #48]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #64]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #72]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #80]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #88]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #96]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #104]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #112]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #120]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #128]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #136]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #144]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #152]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #200]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #208]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #216]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #224]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #232]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #240]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #248]
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ed25519_scalar_reduce:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	movz w4, #0, lsl #0
	movz w5, #0, lsl #0
	movz w6, #0, lsl #0
	movz w7, #0, lsl #0
	movz w10, #0, lsl #0
	movz w19, #64, lsl #0
20:
	sub x19, x19, #8
	add x9, x1, x19
	ldr x3, [x9, #0]
	lsr x12, x6, #60
	lsl x13, x7, #4
	orr x12, x12, x13
	lsr x13, x7, #60
	lsl x7, x6, #4
	lsr x7, x7, #4
	add x6, x5, #0
	add x5, x4, #0
	add x4, x3, #0
	movz x8, #54253, lsl #0
	movk x8, #23797, lsl #16
	movk x8, #25370, lsl #32
	movk x8, #22546, lsl #48
	movz x17, #40150, lsl #0
	movk x17, #41719, lsl #16
	movk x17, #63966, lsl #32
	movk x17, #5342, lsl #48
	mul x14, x12, x8
	umulh x15, x12, x8
	mul x9, x12, x17
	umulh x16, x12, x17
	adds x15, x15, x9
	adcs x16, x16, x10
	mul x9, x13, x8
	mul x13, x13, x17
	adds x15, x15, x9
	adcs x16, x16, x13
	subs x14, x8, x14
	sbcs x15, x17, x15
	sbcs x16, x10, x16
	movz x9, #4096, lsl #48
	sbcs x9, x9, x10
	adds x4, x4, x14
	adcs x5, x5, x15
	adcs x6, x6, x16
	adcs x7, x7, x9
	add x21, x4, #0
	add x22, x5, #0
	add x23, x6, #0
	add x24, x7, #0
	movz x3, #54253, lsl #0
	movk x3, #23797, lsl #16
	movk x3, #25370, lsl #32
	movk x3, #22546, lsl #48
	subs x4, x4, x3
	movz x3, #40150, lsl #0
	movk x3, #41719, lsl #16
	movk x3, #63966, lsl #32
	movk x3, #5342, lsl #48
	sbcs x5, x5, x3
	sbcs x6, x6, x10
	movz x3, #0, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #4096, lsl #48
	sbcs x7, x7, x3
	sbcs x8, x10, x10
	eor x21, x21, x4
	and x21, x21, x8
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x8
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x8
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x8
	eor x7, x7, x24
	cbnz x19, 20b
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	ret
	.p2align 6

vg_ed25519_scalar_base:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	str x0, [x2, #48]
	add x0, x2, #0
	movz w19, #0, lsl #0
	movz w11, #1, lsl #0
20:
	add x8, x1, x19
	ldrb w8, [x8, #0]
	lsl x9, x19, #3
	add x9, x0, x9
	lsr x2, x8, #0
	and x2, x2, x11
	strb w2, [x9, #768]
	lsr x2, x8, #1
	and x2, x2, x11
	strb w2, [x9, #769]
	lsr x2, x8, #2
	and x2, x2, x11
	strb w2, [x9, #770]
	lsr x2, x8, #3
	and x2, x2, x11
	strb w2, [x9, #771]
	lsr x2, x8, #4
	and x2, x2, x11
	strb w2, [x9, #772]
	lsr x2, x8, #5
	and x2, x2, x11
	strb w2, [x9, #773]
	lsr x2, x8, #6
	and x2, x2, x11
	strb w2, [x9, #774]
	lsr x2, x8, #7
	and x2, x2, x11
	strb w2, [x9, #775]
	add x19, x19, #1
	movz x8, #32, lsl #0
	movk x8, #0, lsl #16
	movk x8, #0, lsl #32
	movk x8, #0, lsl #48
	sub x8, x19, x8
	cbnz x8, 20b
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz x4, #19732, lsl #0
	movk x4, #3704, lsl #16
	movk x4, #12927, lsl #32
	movk x4, #9506, lsl #48
	movz x5, #5405, lsl #0
	movk x5, #45271, lsl #16
	movk x5, #55882, lsl #32
	movk x5, #3292, lsl #48
	movz x6, #56252, lsl #0
	movk x6, #36121, lsl #16
	movk x6, #1244, lsl #32
	movk x6, #24478, lsl #48
	movz x7, #6932, lsl #0
	movk x7, #13402, lsl #16
	movk x7, #62822, lsl #32
	movk x7, #2631, lsl #48
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz x4, #63212, lsl #0
	movk x4, #7152, lsl #16
	movk x4, #46503, lsl #32
	movk x4, #42296, lsl #48
	movz x5, #22843, lsl #0
	movk x5, #23337, lsl #16
	movk x5, #47280, lsl #32
	movk x5, #5943, lsl #48
	movz x6, #51705, lsl #0
	movk x6, #39721, lsl #16
	movk x6, #22935, lsl #32
	movk x6, #12652, lsl #48
	movz x7, #638, lsl #0
	movk x7, #13703, lsl #16
	movk x7, #18230, lsl #32
	movk x7, #2371, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #21093, lsl #0
	movk x4, #17697, lsl #16
	movk x4, #18186, lsl #32
	movk x4, #52560, lsl #48
	movz x5, #40439, lsl #0
	movk x5, #3071, lsl #16
	movk x5, #8693, lsl #32
	movk x5, #63940, lsl #48
	movz x6, #32329, lsl #0
	movk x6, #58054, lsl #16
	movk x6, #33041, lsl #32
	movk x6, #3634, lsl #48
	movz x7, #49440, lsl #0
	movk x7, #53819, lsl #16
	movk x7, #38278, lsl #32
	movk x7, #14477, lsl #48
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w19, #0, lsl #0
21:
	lsl x8, x19, #2
	add x8, x0, x8
	ldrb w2, [x8, #771]
	add x2, x2, x2
	ldrb w3, [x8, #770]
	add x2, x2, x3
	add x2, x2, x2
	ldrb w3, [x8, #769]
	add x2, x2, x3
	add x2, x2, x2
	ldrb w3, [x8, #768]
	add x2, x2, x3
	sub x3, x2, #8
	lsr x1, x3, #63
	movz w9, #0, lsl #0
	sub x1, x9, x1
	eor x2, x3, x1
	sub x2, x2, x1
	adrp x9, {VG_ED25519_COMB}
	add x9, x9, {VG_ED25519_COMB}
	lsl x16, x19, #8
	add x9, x9, x16
	add x9, x9, x16
	add x9, x9, x16
	movz x3, #1, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #1, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #0]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #16]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #256]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #272]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #2, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #32]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #48]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #288]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #304]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #3, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #64]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #80]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #320]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #336]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #4, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #96]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #112]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #352]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #368]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #5, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #128]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #144]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #384]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #400]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #6, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #160]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #176]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #416]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #432]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #7, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #192]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #208]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #448]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #464]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	movz x16, #8, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #224]
	csel x3, x16, x3, eq
	csel x4, x17, x4, eq
	ldp x16, x17, [x9, #240]
	csel x5, x16, x5, eq
	csel x6, x17, x6, eq
	ldp x16, x17, [x9, #480]
	csel x7, x16, x7, eq
	csel x8, x17, x8, eq
	ldp x16, x17, [x9, #496]
	csel x10, x16, x10, eq
	csel x11, x17, x11, eq
	add x9, x9, #512
	movz x16, #1, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #0]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #16]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #2, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #32]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #48]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #3, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #64]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #80]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #4, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #96]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #112]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #5, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #128]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #144]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #6, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #160]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #176]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #7, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #192]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #208]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x16, #8, lsl #0
	subs x16, x2, x16
	ldp x16, x17, [x9, #224]
	csel x12, x16, x12, eq
	csel x13, x17, x13, eq
	ldp x16, x17, [x9, #240]
	csel x14, x16, x14, eq
	csel x15, x17, x15, eq
	movz x17, #0, lsl #0
	sub x17, x17, #1
	lsr x24, x17, #1
	sub x16, x17, #18
	subs x20, x16, x12
	sbcs x21, x17, x13
	sbcs x22, x17, x14
	sbc x23, x24, x15
	tst x1, x1
	csel x12, x20, x12, ne
	csel x13, x21, x13, ne
	csel x14, x22, x14, ne
	csel x15, x23, x15, ne
	csel x20, x7, x3, ne
	csel x21, x8, x4, ne
	csel x22, x10, x5, ne
	csel x23, x11, x6, ne
	csel x16, x3, x7, ne
	csel x17, x4, x8, ne
	csel x24, x5, x10, ne
	csel x2, x6, x11, ne
	stp x20, x21, [x0, #192]
	stp x22, x23, [x0, #208]
	stp x16, x17, [x0, #224]
	stp x24, x2, [x0, #240]
	stp x12, x13, [x0, #256]
	stp x14, x15, [x0, #272]
	movz x17, #0, lsl #0
	ldp x3, x4, [x0, #128]
	ldp x7, x8, [x0, #128]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #144]
	ldp x7, x8, [x0, #144]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #288]
	stp x5, x6, [x0, #304]
	ldp x5, x6, [x0, #96]
	ldp x4, x3, [x0, #64]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #112]
	ldp x4, x3, [x0, #80]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #320]
	stp x7, x8, [x0, #336]
	ldp x3, x4, [x0, #96]
	ldp x7, x8, [x0, #64]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #112]
	ldp x7, x8, [x0, #80]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #352]
	stp x5, x6, [x0, #368]
	ldp x3, x4, [x0, #160]
	ldp x7, x8, [x0, #256]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #272]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #176]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #384]
	stp x14, x15, [x0, #400]
	ldp x3, x4, [x0, #320]
	ldp x7, x8, [x0, #192]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #208]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #336]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #320]
	stp x14, x15, [x0, #336]
	ldp x3, x4, [x0, #352]
	ldp x7, x8, [x0, #224]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #240]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #368]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #352]
	stp x14, x15, [x0, #368]
	ldp x5, x6, [x0, #288]
	ldp x4, x3, [x0, #384]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #304]
	ldp x4, x3, [x0, #400]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #416]
	stp x7, x8, [x0, #432]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #384]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #304]
	ldp x7, x8, [x0, #400]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #288]
	stp x5, x6, [x0, #304]
	ldp x5, x6, [x0, #352]
	ldp x4, x3, [x0, #320]
	subs x5, x5, x4
	sbcs x6, x6, x3
	ldp x7, x8, [x0, #368]
	ldp x4, x3, [x0, #336]
	sbcs x7, x7, x4
	sbcs x8, x8, x3
	movz w4, #38, lsl #0
	csel x3, x4, x17, lo
	subs x5, x5, x3
	sbcs x6, x6, x17
	sbcs x7, x7, x17
	sbc x8, x8, x17
	stp x5, x6, [x0, #448]
	stp x7, x8, [x0, #464]
	ldp x3, x4, [x0, #352]
	ldp x7, x8, [x0, #320]
	adds x3, x3, x7
	adcs x4, x4, x8
	ldp x5, x6, [x0, #368]
	ldp x7, x8, [x0, #336]
	adcs x5, x5, x7
	adcs x6, x6, x8
	movz w9, #38, lsl #0
	csel x9, x9, x17, hs
	adds x3, x3, x9
	adcs x4, x4, x17
	adcs x5, x5, x17
	adc x6, x6, x17
	stp x3, x4, [x0, #320]
	stp x5, x6, [x0, #336]
	ldp x3, x4, [x0, #416]
	ldp x7, x8, [x0, #288]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #304]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #432]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #128]
	stp x14, x15, [x0, #144]
	ldp x3, x4, [x0, #448]
	ldp x7, x8, [x0, #416]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #432]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #464]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #64]
	stp x14, x15, [x0, #80]
	ldp x3, x4, [x0, #288]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #304]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #96]
	stp x14, x15, [x0, #112]
	ldp x3, x4, [x0, #448]
	ldp x7, x8, [x0, #320]
	mul x12, x3, x7
	umulh x13, x3, x7
	mul x11, x3, x8
	umulh x14, x3, x8
	adds x13, x13, x11
	ldp x9, x10, [x0, #336]
	mul x11, x3, x9
	umulh x15, x3, x9
	adcs x14, x14, x11
	mul x11, x3, x10
	umulh x16, x3, x10
	adcs x15, x15, x11
	adc x16, x16, x17
	ldp x5, x6, [x0, #464]
	mul x11, x4, x7
	adds x13, x13, x11
	mul x11, x4, x8
	adcs x14, x14, x11
	mul x11, x4, x9
	adcs x15, x15, x11
	mul x11, x4, x10
	adcs x16, x16, x11
	umulh x3, x4, x10
	adc x3, x3, x17
	umulh x11, x4, x7
	adds x14, x14, x11
	umulh x11, x4, x8
	adcs x15, x15, x11
	umulh x11, x4, x9
	adcs x16, x16, x11
	adc x3, x3, x17
	mul x11, x5, x7
	adds x14, x14, x11
	mul x11, x5, x8
	adcs x15, x15, x11
	mul x11, x5, x9
	adcs x16, x16, x11
	mul x11, x5, x10
	adcs x3, x3, x11
	umulh x4, x5, x10
	adc x4, x4, x17
	umulh x11, x5, x7
	adds x15, x15, x11
	umulh x11, x5, x8
	adcs x16, x16, x11
	umulh x11, x5, x9
	adcs x3, x3, x11
	adc x4, x4, x17
	mul x11, x6, x7
	adds x15, x15, x11
	mul x11, x6, x8
	adcs x16, x16, x11
	mul x11, x6, x9
	adcs x3, x3, x11
	mul x11, x6, x10
	adcs x4, x4, x11
	umulh x5, x6, x10
	adc x5, x5, x17
	umulh x11, x6, x7
	adds x16, x16, x11
	umulh x11, x6, x8
	adcs x3, x3, x11
	umulh x11, x6, x9
	adcs x4, x4, x11
	adc x5, x5, x17
	movz w7, #38, lsl #0
	mul x11, x7, x16
	umulh x9, x7, x16
	adds x12, x12, x11
	mul x11, x7, x3
	umulh x3, x7, x3
	adcs x13, x13, x11
	mul x11, x7, x4
	umulh x4, x7, x4
	adcs x14, x14, x11
	mul x11, x7, x5
	umulh x5, x7, x5
	adcs x15, x15, x11
	adc x16, x17, x17
	adds x15, x15, x4
	adc x16, x16, x5
	adds x11, x15, x15
	lsr x15, x11, #1
	adc x8, x16, x16
	movz w7, #19, lsl #0
	mul x11, x7, x8
	adds x12, x12, x11
	adcs x13, x13, x9
	adcs x14, x14, x3
	adc x15, x15, x17
	stp x12, x13, [x0, #160]
	stp x14, x15, [x0, #176]
	add x19, x19, #1
	sub x8, x19, #64
	cbnz x8, 21b
	add x19, x1, #0
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #128]
	ldr x3, [x0, #136]
	ldr x4, [x0, #144]
	ldr x5, [x0, #152]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	adds x8, x2, x6
	adcs x9, x3, x12
	adcs x10, x4, x12
	adc x11, x5, x12
	lsr x13, x11, #63
	and x11, x11, x7
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x10, x10, x4
	and x10, x10, x13
	eor x4, x4, x10
	eor x11, x11, x5
	and x11, x11, x13
	eor x5, x5, x11
	str x2, [x0, #224]
	str x3, [x0, #232]
	str x4, [x0, #240]
	str x5, [x0, #248]
	movz x2, #65517, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #192]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #200]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	str x2, [x0, #208]
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	str x2, [x0, #216]
	str x12, [x0, #256]
	str x12, [x0, #264]
	str x12, [x0, #272]
	str x12, [x0, #280]
	movz x2, #8345, lsl #0
	movk x2, #29954, lsl #16
	movk x2, #40483, lsl #32
	movk x2, #41209, lsl #48
	str x2, [x0, #288]
	movz x2, #9621, lsl #0
	movk x2, #7443, lsl #16
	movk x2, #36671, lsl #32
	movk x2, #43206, lsl #48
	str x2, [x0, #296]
	movz x2, #21058, lsl #0
	movk x2, #1452, lsl #16
	movk x2, #35128, lsl #32
	movk x2, #27756, lsl #48
	str x2, [x0, #304]
	movz x2, #1557, lsl #0
	movk x2, #16759, lsl #16
	movk x2, #2226, lsl #32
	movk x2, #10085, lsl #48
	str x2, [x0, #312]
	movz x1, #1, lsl #0
	str x1, [x0, #480]
	movz x20, #10, lsl #0
22:
	ldr x1, [x0, #480]
	ldr x2, [x0, #192]
	ldr x3, [x0, #224]
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	str x1, [x0, #480]
	movz x12, #0, lsl #0
	lsr x14, x4, #63
	sub x14, x12, x14
	eor x4, x4, x14
	sub x4, x4, x14
	lsr x15, x5, #63
	sub x15, x12, x15
	eor x5, x5, x15
	sub x5, x5, x15
	lsr x16, x6, #63
	sub x16, x12, x16
	eor x6, x6, x16
	sub x6, x6, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	eor x7, x7, x17
	sub x7, x7, x17
	and x8, x4, x14
	and x9, x5, x15
	add x13, x8, x9
	and x8, x6, x16
	and x9, x7, x17
	add x11, x8, x9
	ldr x8, [x0, #192]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #320]
	ldr x8, [x0, #200]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #328]
	ldr x8, [x0, #208]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #336]
	ldr x8, [x0, #216]
	eor x8, x8, x14
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x15
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #344]
	str x3, [x0, #352]
	ldr x8, [x0, #192]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #224]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #360]
	ldr x8, [x0, #200]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #232]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #368]
	ldr x8, [x0, #208]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #240]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #376]
	ldr x8, [x0, #216]
	eor x8, x8, x16
	lsr x3, x8, #63
	sub x3, x12, x3
	and x3, x3, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #248]
	eor x8, x8, x17
	lsr x2, x8, #63
	sub x2, x12, x2
	and x2, x2, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #384]
	str x3, [x0, #392]
	ldr x8, [x0, #256]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x13, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #400]
	ldr x8, [x0, #264]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #408]
	ldr x8, [x0, #272]
	eor x8, x8, x14
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x15
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #416]
	ldr x8, [x0, #280]
	eor x8, x8, x14
	and x3, x14, x4
	sub x3, x12, x3
	mul x9, x8, x4
	umulh x10, x8, x4
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x15
	and x2, x15, x5
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x5
	umulh x10, x8, x5
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #424]
	str x3, [x0, #432]
	ldr x8, [x0, #256]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x11, x9
	adc x2, x12, x10
	ldr x8, [x0, #288]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #440]
	ldr x8, [x0, #264]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #296]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #448]
	ldr x8, [x0, #272]
	eor x8, x8, x16
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x2, x12, x10
	ldr x8, [x0, #304]
	eor x8, x8, x17
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x2, x2, x10
	str x1, [x0, #456]
	ldr x8, [x0, #280]
	eor x8, x8, x16
	and x3, x16, x6
	sub x3, x12, x3
	mul x9, x8, x6
	umulh x10, x8, x6
	adds x1, x2, x9
	adc x3, x3, x10
	ldr x8, [x0, #312]
	eor x8, x8, x17
	and x2, x17, x7
	sub x2, x12, x2
	add x3, x3, x2
	mul x9, x8, x7
	umulh x10, x8, x7
	adds x1, x1, x9
	adc x3, x3, x10
	str x1, [x0, #464]
	str x3, [x0, #472]
	ldr x1, [x0, #320]
	ldr x2, [x0, #328]
	ldr x3, [x0, #336]
	ldr x8, [x0, #344]
	ldr x9, [x0, #352]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #192]
	str x2, [x0, #200]
	str x3, [x0, #208]
	str x8, [x0, #216]
	ldr x1, [x0, #360]
	ldr x2, [x0, #368]
	ldr x3, [x0, #376]
	ldr x8, [x0, #384]
	ldr x9, [x0, #392]
	extr x1, x2, x1, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	str x1, [x0, #224]
	str x2, [x0, #232]
	str x3, [x0, #240]
	str x8, [x0, #248]
	movz x13, #19, lsl #0
	ldr x1, [x0, #400]
	ldr x2, [x0, #408]
	ldr x3, [x0, #416]
	ldr x8, [x0, #424]
	ldr x9, [x0, #432]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #256]
	str x2, [x0, #264]
	str x3, [x0, #272]
	str x8, [x0, #280]
	ldr x1, [x0, #440]
	ldr x2, [x0, #448]
	ldr x3, [x0, #456]
	ldr x8, [x0, #464]
	ldr x9, [x0, #472]
	extr x10, x9, x8, #63
	lsr x11, x9, #63
	sub x10, x10, x11
	lsl x11, x10, #63
	add x8, x8, x11
	lsr x14, x10, #63
	sub x14, x12, x14
	mul x9, x10, x13
	umulh x11, x10, x13
	and x15, x14, x13
	sub x11, x11, x15
	adds x1, x1, x9
	adcs x2, x2, x11
	adcs x3, x3, x14
	adc x8, x8, x14
	str x1, [x0, #288]
	str x2, [x0, #296]
	str x3, [x0, #304]
	str x8, [x0, #312]
	sub x20, x20, #1
	cbnz x20, 22b
	movz x12, #0, lsl #0
	movz x6, #19, lsl #0
	movz x7, #65535, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65535, lsl #32
	movk x7, #32767, lsl #48
	ldr x2, [x0, #256]
	ldr x3, [x0, #264]
	ldr x4, [x0, #272]
	ldr x5, [x0, #280]
	lsr x8, x5, #63
	and x5, x5, x7
	mul x8, x8, x6
	adds x2, x2, x8
	adcs x3, x3, x12
	adcs x4, x4, x12
	adc x5, x5, x12
	movz x9, #65498, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	subs x8, x9, x2
	sbcs x9, x10, x3
	sbcs x11, x10, x4
	sbc x10, x10, x5
	ldr x13, [x0, #216]
	lsr x13, x13, #63
	sub x13, x12, x13
	eor x8, x8, x2
	and x8, x8, x13
	eor x2, x2, x8
	eor x9, x9, x3
	and x9, x9, x13
	eor x3, x3, x9
	eor x11, x11, x4
	and x11, x11, x13
	eor x4, x4, x11
	eor x10, x10, x5
	and x10, x10, x13
	eor x5, x5, x10
	str x2, [x0, #544]
	str x3, [x0, #552]
	str x4, [x0, #560]
	str x5, [x0, #568]
	add x1, x19, #0
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	movz w9, #1, lsl #0
	and x19, x4, x9
	lsl x19, x19, #63
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	add x7, x7, x19
	add x2, x0, #0
	ldr x0, [x0, #48]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	ret
	.p2align 6

vg_ed25519_verify_equation:
	add x8, x2, #0
	add x2, x3, #0
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	str x0, [x2, #7936]
	str x1, [x2, #7944]
	str x8, [x2, #7952]
	add x0, x2, #0
	ldr x2, [x0, #7944]
	add x2, x2, #32
	movz w10, #0, lsl #0
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	add x21, x4, #0
	add x22, x5, #0
	add x23, x6, #0
	add x24, x7, #0
	movz x3, #54253, lsl #0
	movk x3, #23797, lsl #16
	movk x3, #25370, lsl #32
	movk x3, #22546, lsl #48
	subs x4, x4, x3
	movz x3, #40150, lsl #0
	movk x3, #41719, lsl #16
	movk x3, #63966, lsl #32
	movk x3, #5342, lsl #48
	sbcs x5, x5, x3
	sbcs x6, x6, x10
	movz x3, #0, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #4096, lsl #48
	sbcs x7, x7, x3
	sbcs x8, x10, x10
	cbnz x8, 20f
	movz w8, #0, lsl #0
	b 21f
20:
	movz w19, #1, lsl #0
	str x19, [x0, #7680]
22:
	ldr x19, [x0, #7680]
	lsl x2, x19, #3
	add x2, x2, x0
	ldr x2, [x2, #7936]
	ldr x1, [x2, #24]
	lsr x1, x1, #63
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	movz x8, #65535, lsl #0
	movk x8, #65535, lsl #16
	movk x8, #65535, lsl #32
	movk x8, #32767, lsl #48
	and x7, x7, x8
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	cbz x8, 23f
	movz w8, #0, lsl #0
	b 24f
23:
	movz x4, #30883, lsl #0
	movk x4, #4953, lsl #16
	movk x4, #19914, lsl #32
	movk x4, #30187, lsl #48
	movz x5, #55467, lsl #0
	movk x5, #16705, lsl #16
	movk x5, #2637, lsl #32
	movk x5, #112, lsl #48
	movz x6, #59544, lsl #0
	movk x6, #30585, lsl #16
	movk x6, #16505, lsl #32
	movk x6, #36039, lsl #48
	movz x7, #65139, lsl #0
	movk x7, #11119, lsl #16
	movk x7, #27886, lsl #32
	movk x7, #20995, lsl #48
	str x4, [x0, #576]
	str x5, [x0, #584]
	str x6, [x0, #592]
	str x7, [x0, #600]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #192]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #200]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #208]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #216]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #576]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #584]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #592]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #600]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #288]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #296]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #304]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #312]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #288]
	ldr x9, [x0, #192]
	adds x4, x4, x9
	ldr x5, [x0, #296]
	ldr x9, [x0, #200]
	adcs x5, x5, x9
	ldr x6, [x0, #304]
	ldr x9, [x0, #208]
	adcs x6, x6, x9
	ldr x7, [x0, #312]
	ldr x9, [x0, #216]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #352]
	ldr x13, [x0, #360]
	ldr x14, [x0, #368]
	ldr x15, [x0, #376]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #384]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #392]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #400]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #408]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #384]
	ldr x13, [x0, #392]
	ldr x14, [x0, #400]
	ldr x15, [x0, #408]
	ldr x3, [x0, #256]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #264]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #272]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #280]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	mov v31.d[0], x30
	bl {vg_gf25519_r64_pow250}
	umov x30, v31.d[0]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz x19, #1, lsl #0
	movk x19, #0, lsl #16
	movk x19, #0, lsl #32
	movk x19, #0, lsl #48
25:
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	sub x19, x19, #1
	cbnz x19, 25b
	movz w10, #0, lsl #0
	ldr x12, [x0, #128]
	ldr x13, [x0, #136]
	ldr x14, [x0, #144]
	ldr x15, [x0, #152]
	ldr x3, [x0, #544]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #552]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #560]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #568]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #256]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #264]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #272]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #280]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	ldr x12, [x0, #352]
	ldr x13, [x0, #360]
	ldr x14, [x0, #368]
	ldr x15, [x0, #376]
	ldr x3, [x0, #256]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #264]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #272]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #280]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #64]
	ldr x13, [x0, #72]
	ldr x14, [x0, #80]
	ldr x15, [x0, #88]
	ldr x3, [x0, #288]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #296]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #304]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #312]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	ldr x12, [x0, #64]
	ldr x13, [x0, #72]
	ldr x14, [x0, #80]
	ldr x15, [x0, #88]
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #256]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #264]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #272]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #280]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x6, [x0, #752]
	ldr x7, [x0, #760]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 26f
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #448]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #456]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #464]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #472]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x6, [x0, #752]
	ldr x7, [x0, #760]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 28f
	movz w8, #0, lsl #0
	b 29f
28:
	movz x4, #41136, lsl #0
	movk x4, #18958, lsl #16
	movk x4, #6951, lsl #32
	movk x4, #50414, lsl #48
	movz x5, #58488, lsl #0
	movk x5, #44335, lsl #16
	movk x5, #6150, lsl #32
	movk x5, #12099, lsl #48
	movz x6, #55207, lsl #0
	movk x6, #15867, lsl #16
	movk x6, #153, lsl #32
	movk x6, #11085, lsl #48
	movz x7, #57099, lsl #0
	movk x7, #20417, lsl #16
	movk x7, #9344, lsl #32
	movk x7, #11139, lsl #48
	str x4, [x0, #640]
	str x5, [x0, #648]
	str x6, [x0, #656]
	str x7, [x0, #664]
	movz w10, #0, lsl #0
	ldr x12, [x0, #640]
	ldr x13, [x0, #648]
	ldr x14, [x0, #656]
	ldr x15, [x0, #664]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 210f
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	movz w9, #1, lsl #0
	and x8, x4, x9
	eor x8, x8, x1
	cbz x8, 212f
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	b 213f
212:
213:
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w8, #1, lsl #0
	b 211f
210:
	cbnz x1, 214f
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	movz w9, #1, lsl #0
	and x8, x4, x9
	eor x8, x8, x1
	cbz x8, 216f
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	b 217f
216:
217:
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w8, #1, lsl #0
	b 215f
214:
	movz w8, #0, lsl #0
215:
211:
29:
	b 27f
26:
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 218f
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	movz w9, #1, lsl #0
	and x8, x4, x9
	eor x8, x8, x1
	cbz x8, 220f
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	b 221f
220:
221:
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w8, #1, lsl #0
	b 219f
218:
	cbnz x1, 222f
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	movz w9, #1, lsl #0
	and x8, x4, x9
	eor x8, x8, x1
	cbz x8, 224f
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #224]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #232]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #240]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #248]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	b 225f
224:
225:
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w8, #1, lsl #0
	b 223f
222:
	movz w8, #0, lsl #0
223:
219:
27:
24:
	cbnz x8, 226f
	movz w8, #0, lsl #0
	movz w19, #0, lsl #0
	b 227f
226:
	ldr x19, [x0, #7680]
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #7424, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x8, #0]
	str x5, [x8, #8]
	str x6, [x8, #16]
	str x7, [x8, #24]
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	str x4, [x8, #32]
	str x5, [x8, #40]
	str x6, [x8, #48]
	str x7, [x8, #56]
	ldr x4, [x0, #128]
	ldr x5, [x0, #136]
	ldr x6, [x0, #144]
	ldr x7, [x0, #152]
	str x4, [x8, #64]
	str x5, [x8, #72]
	str x6, [x8, #80]
	str x7, [x8, #88]
	ldr x4, [x0, #160]
	ldr x5, [x0, #168]
	ldr x6, [x0, #176]
	ldr x7, [x0, #184]
	str x4, [x8, #96]
	str x5, [x8, #104]
	str x6, [x8, #112]
	str x7, [x8, #120]
	sub x9, x19, #1
	str x9, [x0, #7680]
	movz w8, #1, lsl #0
227:
	cbnz x19, 22b
	cbnz x8, 228f
	movz w8, #0, lsl #0
	b 229f
228:
	movz x4, #30883, lsl #0
	movk x4, #4953, lsl #16
	movk x4, #19914, lsl #32
	movk x4, #30187, lsl #48
	movz x5, #55467, lsl #0
	movk x5, #16705, lsl #16
	movk x5, #2637, lsl #32
	movk x5, #112, lsl #48
	movz x6, #59544, lsl #0
	movk x6, #30585, lsl #16
	movk x6, #16505, lsl #32
	movk x6, #36039, lsl #48
	movz x7, #65139, lsl #0
	movk x7, #11119, lsl #16
	movk x7, #27886, lsl #32
	movk x7, #20995, lsl #48
	str x4, [x0, #576]
	str x5, [x0, #584]
	str x6, [x0, #592]
	str x7, [x0, #600]
	movz w19, #0, lsl #0
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #7424, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w19, #0, lsl #0
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x0, #608]
	str x5, [x0, #616]
	str x6, [x0, #624]
	str x7, [x0, #632]
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	str x4, [x0, #640]
	str x5, [x0, #648]
	str x6, [x0, #656]
	str x7, [x0, #664]
	ldr x4, [x0, #128]
	ldr x5, [x0, #136]
	ldr x6, [x0, #144]
	ldr x7, [x0, #152]
	str x4, [x0, #672]
	str x5, [x0, #680]
	str x6, [x0, #688]
	str x7, [x0, #696]
	ldr x4, [x0, #160]
	ldr x5, [x0, #168]
	ldr x6, [x0, #176]
	ldr x7, [x0, #184]
	str x4, [x0, #704]
	str x5, [x0, #712]
	str x6, [x0, #720]
	str x7, [x0, #728]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #640]
	ldr x9, [x0, #608]
	subs x4, x4, x9
	ldr x5, [x0, #648]
	ldr x9, [x0, #616]
	sbcs x5, x5, x9
	ldr x6, [x0, #656]
	ldr x9, [x0, #624]
	sbcs x6, x6, x9
	ldr x7, [x0, #664]
	ldr x9, [x0, #632]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #640]
	ldr x9, [x0, #608]
	adds x4, x4, x9
	ldr x5, [x0, #648]
	ldr x9, [x0, #616]
	adcs x5, x5, x9
	ldr x6, [x0, #656]
	ldr x9, [x0, #624]
	adcs x6, x6, x9
	ldr x7, [x0, #664]
	ldr x9, [x0, #632]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #704]
	ldr x9, [x0, #704]
	adds x4, x4, x9
	ldr x5, [x0, #712]
	ldr x9, [x0, #712]
	adcs x5, x5, x9
	ldr x6, [x0, #720]
	ldr x9, [x0, #720]
	adcs x6, x6, x9
	ldr x7, [x0, #728]
	ldr x9, [x0, #728]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #576]
	ldr x13, [x0, #584]
	ldr x14, [x0, #592]
	ldr x15, [x0, #600]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #672]
	ldr x9, [x0, #672]
	adds x4, x4, x9
	ldr x5, [x0, #680]
	ldr x9, [x0, #680]
	adcs x5, x5, x9
	ldr x6, [x0, #688]
	ldr x9, [x0, #688]
	adcs x6, x6, x9
	ldr x7, [x0, #696]
	ldr x9, [x0, #696]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #5376, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x8, #0]
	str x5, [x8, #8]
	str x6, [x8, #16]
	str x7, [x8, #24]
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	str x4, [x8, #32]
	str x5, [x8, #40]
	str x6, [x8, #48]
	str x7, [x8, #56]
	ldr x4, [x0, #128]
	ldr x5, [x0, #136]
	ldr x6, [x0, #144]
	ldr x7, [x0, #152]
	str x4, [x8, #64]
	str x5, [x8, #72]
	str x6, [x8, #80]
	str x7, [x8, #88]
	ldr x4, [x0, #160]
	ldr x5, [x0, #168]
	ldr x6, [x0, #176]
	ldr x7, [x0, #184]
	str x4, [x8, #96]
	str x5, [x8, #104]
	str x6, [x8, #112]
	str x7, [x8, #120]
	ldr x4, [x0, #608]
	ldr x5, [x0, #616]
	ldr x6, [x0, #624]
	ldr x7, [x0, #632]
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x0, #640]
	ldr x5, [x0, #648]
	ldr x6, [x0, #656]
	ldr x7, [x0, #664]
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	ldr x4, [x0, #672]
	ldr x5, [x0, #680]
	ldr x6, [x0, #688]
	ldr x7, [x0, #696]
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	ldr x4, [x0, #704]
	ldr x5, [x0, #712]
	ldr x6, [x0, #720]
	ldr x7, [x0, #728]
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #5376, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w19, #1, lsl #0
230:
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #192]
	ldr x13, [x0, #200]
	ldr x14, [x0, #208]
	ldr x15, [x0, #216]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	adds x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	adcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	adcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #224]
	ldr x13, [x0, #232]
	ldr x14, [x0, #240]
	ldr x15, [x0, #248]
	ldr x3, [x0, #352]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #360]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #368]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #376]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #160]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #168]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #176]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #184]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	adds x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	adcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	adcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #512]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #520]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #528]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #536]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x0, #608]
	str x5, [x0, #616]
	str x6, [x0, #624]
	str x7, [x0, #632]
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	str x4, [x0, #640]
	str x5, [x0, #648]
	str x6, [x0, #656]
	str x7, [x0, #664]
	ldr x4, [x0, #128]
	ldr x5, [x0, #136]
	ldr x6, [x0, #144]
	ldr x7, [x0, #152]
	str x4, [x0, #672]
	str x5, [x0, #680]
	str x6, [x0, #688]
	str x7, [x0, #696]
	ldr x4, [x0, #160]
	ldr x5, [x0, #168]
	ldr x6, [x0, #176]
	ldr x7, [x0, #184]
	str x4, [x0, #704]
	str x5, [x0, #712]
	str x6, [x0, #720]
	str x7, [x0, #728]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #640]
	ldr x9, [x0, #608]
	subs x4, x4, x9
	ldr x5, [x0, #648]
	ldr x9, [x0, #616]
	sbcs x5, x5, x9
	ldr x6, [x0, #656]
	ldr x9, [x0, #624]
	sbcs x6, x6, x9
	ldr x7, [x0, #664]
	ldr x9, [x0, #632]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #640]
	ldr x9, [x0, #608]
	adds x4, x4, x9
	ldr x5, [x0, #648]
	ldr x9, [x0, #616]
	adcs x5, x5, x9
	ldr x6, [x0, #656]
	ldr x9, [x0, #624]
	adcs x6, x6, x9
	ldr x7, [x0, #664]
	ldr x9, [x0, #632]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #704]
	ldr x9, [x0, #704]
	adds x4, x4, x9
	ldr x5, [x0, #712]
	ldr x9, [x0, #712]
	adcs x5, x5, x9
	ldr x6, [x0, #720]
	ldr x9, [x0, #720]
	adcs x6, x6, x9
	ldr x7, [x0, #728]
	ldr x9, [x0, #728]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #576]
	ldr x13, [x0, #584]
	ldr x14, [x0, #592]
	ldr x15, [x0, #600]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #672]
	ldr x9, [x0, #672]
	adds x4, x4, x9
	ldr x5, [x0, #680]
	ldr x9, [x0, #680]
	adcs x5, x5, x9
	ldr x6, [x0, #688]
	ldr x9, [x0, #688]
	adcs x6, x6, x9
	ldr x7, [x0, #696]
	ldr x9, [x0, #696]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #5376, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	str x4, [x8, #0]
	str x5, [x8, #8]
	str x6, [x8, #16]
	str x7, [x8, #24]
	ldr x4, [x0, #96]
	ldr x5, [x0, #104]
	ldr x6, [x0, #112]
	ldr x7, [x0, #120]
	str x4, [x8, #32]
	str x5, [x8, #40]
	str x6, [x8, #48]
	str x7, [x8, #56]
	ldr x4, [x0, #128]
	ldr x5, [x0, #136]
	ldr x6, [x0, #144]
	ldr x7, [x0, #152]
	str x4, [x8, #64]
	str x5, [x8, #72]
	str x6, [x8, #80]
	str x7, [x8, #88]
	ldr x4, [x0, #160]
	ldr x5, [x0, #168]
	ldr x6, [x0, #176]
	ldr x7, [x0, #184]
	str x4, [x8, #96]
	str x5, [x8, #104]
	str x6, [x8, #112]
	str x7, [x8, #120]
	ldr x4, [x0, #608]
	ldr x5, [x0, #616]
	ldr x6, [x0, #624]
	ldr x7, [x0, #632]
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x0, #640]
	ldr x5, [x0, #648]
	ldr x6, [x0, #656]
	ldr x7, [x0, #664]
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	ldr x4, [x0, #672]
	ldr x5, [x0, #680]
	ldr x6, [x0, #688]
	ldr x7, [x0, #696]
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	ldr x4, [x0, #704]
	ldr x5, [x0, #712]
	ldr x6, [x0, #720]
	ldr x7, [x0, #728]
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	add x19, x19, #1
	sub x8, x19, #15
	cbnz x8, 230b
	adrp x9, {VG_ED25519_VERIFY_NEG_BASE}
	add x9, x9, {VG_ED25519_VERIFY_NEG_BASE}
	movz w19, #0, lsl #0
231:
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #2048, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x9, #0]
	ldr x5, [x9, #8]
	ldr x6, [x9, #16]
	ldr x7, [x9, #24]
	str x4, [x8, #0]
	str x5, [x8, #8]
	str x6, [x8, #16]
	str x7, [x8, #24]
	ldr x4, [x9, #32]
	ldr x5, [x9, #40]
	ldr x6, [x9, #48]
	ldr x7, [x9, #56]
	str x4, [x8, #32]
	str x5, [x8, #40]
	str x6, [x8, #48]
	str x7, [x8, #56]
	ldr x4, [x9, #64]
	ldr x5, [x9, #72]
	ldr x6, [x9, #80]
	ldr x7, [x9, #88]
	str x4, [x8, #64]
	str x5, [x8, #72]
	str x6, [x8, #80]
	str x7, [x8, #88]
	ldr x4, [x9, #96]
	ldr x5, [x9, #104]
	ldr x6, [x9, #112]
	ldr x7, [x9, #120]
	str x4, [x8, #96]
	str x5, [x8, #104]
	str x6, [x8, #112]
	str x7, [x8, #120]
	add x9, x9, #128
	add x19, x19, #1
	sub x8, x19, #15
	cbnz x8, 231b
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz x8, #128, lsl #0
	movk x8, #0, lsl #16
	movk x8, #0, lsl #32
	movk x8, #0, lsl #48
	str x8, [x0, #56]
	ldr x2, [x0, #7952]
	movz w8, #15, lsl #0
	dup v7.16b, w8
	ldr q0, [x2, #0]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #768]
	str q3, [x0, #784]
	ldr q0, [x2, #16]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #800]
	str q3, [x0, #816]
	ldr q0, [x2, #32]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #832]
	str q3, [x0, #848]
	ldr q0, [x2, #48]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #864]
	str q3, [x0, #880]
	ldr x2, [x0, #7944]
	ldr q0, [x2, #32]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #896]
	str q3, [x0, #912]
	ldr q0, [x2, #48]
	ushr v1.16b, v0.16b, #4
	and v0.16b, v0.16b, v7.16b
	zip1 v2.16b, v0.16b, v1.16b
	zip2 v3.16b, v0.16b, v1.16b
	str q2, [x0, #928]
	str q3, [x0, #944]
232:
	ldr x8, [x0, #56]
	sub x8, x8, #1
	add x2, x0, x8
	ldrb w19, [x2, #768]
	cbnz x19, 233f
	str x8, [x0, #56]
	sub x19, x8, #64
	b 234f
233:
	movz w19, #0, lsl #0
234:
	cbnz x19, 232b
	ldr x19, [x0, #56]
	sub x19, x19, #64
	cbnz x19, 235f
	b 236f
235:
237:
	ldr x19, [x0, #56]
	sub x19, x19, #1
	str x19, [x0, #56]
	movz w1, #4, lsl #0
238:
	movz w10, #0, lsl #0
	ldr x12, [x0, #64]
	ldr x13, [x0, #72]
	ldr x14, [x0, #80]
	ldr x15, [x0, #88]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #128]
	ldr x13, [x0, #136]
	ldr x14, [x0, #144]
	ldr x15, [x0, #152]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #384]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #392]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #400]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #408]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #416]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #424]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #432]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #440]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #384]
	ldr x9, [x0, #448]
	subs x4, x4, x9
	ldr x5, [x0, #392]
	ldr x9, [x0, #456]
	sbcs x5, x5, x9
	ldr x6, [x0, #400]
	ldr x9, [x0, #464]
	sbcs x6, x6, x9
	ldr x7, [x0, #408]
	ldr x9, [x0, #472]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #320]
	ldr x9, [x0, #352]
	adds x4, x4, x9
	ldr x5, [x0, #328]
	ldr x9, [x0, #360]
	adcs x5, x5, x9
	ldr x6, [x0, #336]
	ldr x9, [x0, #368]
	adcs x6, x6, x9
	ldr x7, [x0, #344]
	ldr x9, [x0, #376]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #448]
	ldr x13, [x0, #456]
	ldr x14, [x0, #464]
	ldr x15, [x0, #472]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	sub x1, x1, #1
	cbnz x1, 238b
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	ldr x8, [x0, #56]
	add x8, x0, x8
	ldrb w19, [x8, #768]
	cbnz x19, 239f
	b 240f
239:
	sub x19, x19, #1
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #5376, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #192]
	ldr x13, [x0, #200]
	ldr x14, [x0, #208]
	ldr x15, [x0, #216]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	adds x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	adcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	adcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #224]
	ldr x13, [x0, #232]
	ldr x14, [x0, #240]
	ldr x15, [x0, #248]
	ldr x3, [x0, #352]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #360]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #368]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #376]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #160]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #168]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #176]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #184]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	adds x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	adcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	adcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #512]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #520]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #528]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #536]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
240:
	ldr x19, [x0, #56]
	sub x19, x19, #64
	cbnz x19, 237b
236:
241:
	ldr x19, [x0, #56]
	sub x19, x19, #1
	str x19, [x0, #56]
	movz w1, #4, lsl #0
242:
	movz w10, #0, lsl #0
	ldr x12, [x0, #64]
	ldr x13, [x0, #72]
	ldr x14, [x0, #80]
	ldr x15, [x0, #88]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #128]
	ldr x13, [x0, #136]
	ldr x14, [x0, #144]
	ldr x15, [x0, #152]
	mul x5, x12, x13
	mul x6, x12, x14
	mul x7, x12, x15
	umulh x2, x12, x13
	umulh x8, x12, x14
	umulh x9, x12, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x9, x10
	mul x2, x13, x14
	mul x8, x13, x15
	umulh x9, x13, x14
	umulh x16, x13, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x16, x10
	adds x21, x21, x9
	adcs x22, x22, x10
	mul x2, x14, x15
	umulh x8, x14, x15
	adds x22, x22, x2
	adcs x23, x8, x10
	adds x5, x5, x5
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x10, x10
	mul x4, x12, x12
	umulh x2, x12, x12
	mul x8, x13, x13
	umulh x9, x13, x13
	mul x16, x14, x14
	umulh x17, x14, x14
	mul x3, x15, x15
	umulh x11, x15, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x22, x17
	adcs x23, x23, x3
	adcs x24, x24, x11
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #384]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #392]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #400]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #408]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #96]
	ldr x13, [x0, #104]
	ldr x14, [x0, #112]
	ldr x15, [x0, #120]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #416]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #424]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #432]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #440]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #384]
	ldr x9, [x0, #448]
	subs x4, x4, x9
	ldr x5, [x0, #392]
	ldr x9, [x0, #456]
	sbcs x5, x5, x9
	ldr x6, [x0, #400]
	ldr x9, [x0, #464]
	sbcs x6, x6, x9
	ldr x7, [x0, #408]
	ldr x9, [x0, #472]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #320]
	ldr x9, [x0, #352]
	adds x4, x4, x9
	ldr x5, [x0, #328]
	ldr x9, [x0, #360]
	adcs x5, x5, x9
	ldr x6, [x0, #336]
	ldr x9, [x0, #368]
	adcs x6, x6, x9
	ldr x7, [x0, #344]
	ldr x9, [x0, #376]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #448]
	ldr x13, [x0, #456]
	ldr x14, [x0, #464]
	ldr x15, [x0, #472]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	sub x1, x1, #1
	cbnz x1, 242b
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #416]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #424]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #432]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #440]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	ldr x8, [x0, #56]
	add x8, x0, x8
	ldrb w19, [x8, #768]
	cbnz x19, 243f
	b 244f
243:
	sub x19, x19, #1
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #5376, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #192]
	ldr x13, [x0, #200]
	ldr x14, [x0, #208]
	ldr x15, [x0, #216]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	adds x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	adcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	adcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #224]
	ldr x13, [x0, #232]
	ldr x14, [x0, #240]
	ldr x15, [x0, #248]
	ldr x3, [x0, #352]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #360]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #368]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #376]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #160]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #168]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #176]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #184]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	adds x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	adcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	adcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #512]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #520]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #528]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #536]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
244:
	ldr x8, [x0, #56]
	add x8, x0, x8
	ldrb w19, [x8, #896]
	cbnz x19, 245f
	b 246f
245:
	sub x19, x19, #1
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #2048, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	subs x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	sbcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	sbcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #192]
	ldr x13, [x0, #200]
	ldr x14, [x0, #208]
	ldr x15, [x0, #216]
	ldr x3, [x0, #320]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #328]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #336]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #344]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #96]
	ldr x9, [x0, #64]
	adds x4, x4, x9
	ldr x5, [x0, #104]
	ldr x9, [x0, #72]
	adcs x5, x5, x9
	ldr x6, [x0, #112]
	ldr x9, [x0, #80]
	adcs x6, x6, x9
	ldr x7, [x0, #120]
	ldr x9, [x0, #88]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #224]
	ldr x13, [x0, #232]
	ldr x14, [x0, #240]
	ldr x15, [x0, #248]
	ldr x3, [x0, #352]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #360]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #368]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #376]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #160]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #168]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #176]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #184]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x3, [x0, #128]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #136]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #144]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #152]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	subs x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	sbcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	sbcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #448]
	str x5, [x0, #456]
	str x6, [x0, #464]
	str x7, [x0, #472]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	subs x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	sbcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	sbcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	str x4, [x0, #480]
	str x5, [x0, #488]
	str x6, [x0, #496]
	str x7, [x0, #504]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #416]
	ldr x9, [x0, #384]
	adds x4, x4, x9
	ldr x5, [x0, #424]
	ldr x9, [x0, #392]
	adcs x5, x5, x9
	ldr x6, [x0, #432]
	ldr x9, [x0, #400]
	adcs x6, x6, x9
	ldr x7, [x0, #440]
	ldr x9, [x0, #408]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #512]
	str x5, [x0, #520]
	str x6, [x0, #528]
	str x7, [x0, #536]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #352]
	ldr x9, [x0, #320]
	adds x4, x4, x9
	ldr x5, [x0, #360]
	ldr x9, [x0, #328]
	adcs x5, x5, x9
	ldr x6, [x0, #368]
	ldr x9, [x0, #336]
	adcs x6, x6, x9
	ldr x7, [x0, #376]
	ldr x9, [x0, #344]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	str x4, [x0, #544]
	str x5, [x0, #552]
	str x6, [x0, #560]
	str x7, [x0, #568]
	movz w10, #0, lsl #0
	ldr x12, [x0, #480]
	ldr x13, [x0, #488]
	ldr x14, [x0, #496]
	ldr x15, [x0, #504]
	ldr x3, [x0, #448]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #456]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #464]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #472]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #512]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #520]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #528]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #536]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	ldr x12, [x0, #512]
	ldr x13, [x0, #520]
	ldr x14, [x0, #528]
	ldr x15, [x0, #536]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
246:
	ldr x19, [x0, #56]
	cbnz x19, 241b
	movz w19, #0, lsl #0
	lsl x8, x19, #7
	add x8, x8, x0
	movz x3, #7552, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x8, x8, x3
	ldr x4, [x8, #0]
	ldr x5, [x8, #8]
	ldr x6, [x8, #16]
	ldr x7, [x8, #24]
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	ldr x4, [x8, #32]
	ldr x5, [x8, #40]
	ldr x6, [x8, #48]
	ldr x7, [x8, #56]
	str x4, [x0, #224]
	str x5, [x0, #232]
	str x6, [x0, #240]
	str x7, [x0, #248]
	ldr x4, [x8, #64]
	ldr x5, [x8, #72]
	ldr x6, [x8, #80]
	ldr x7, [x8, #88]
	str x4, [x0, #256]
	str x5, [x0, #264]
	str x6, [x0, #272]
	str x7, [x0, #280]
	ldr x4, [x8, #96]
	ldr x5, [x8, #104]
	ldr x6, [x8, #112]
	ldr x7, [x8, #120]
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #320]
	ldr x9, [x0, #192]
	subs x4, x4, x9
	ldr x5, [x0, #328]
	ldr x9, [x0, #200]
	sbcs x5, x5, x9
	ldr x6, [x0, #336]
	ldr x9, [x0, #208]
	sbcs x6, x6, x9
	ldr x7, [x0, #344]
	ldr x9, [x0, #216]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #192]
	str x5, [x0, #200]
	str x6, [x0, #208]
	str x7, [x0, #216]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #320]
	ldr x9, [x0, #288]
	subs x4, x4, x9
	ldr x5, [x0, #328]
	ldr x9, [x0, #296]
	sbcs x5, x5, x9
	ldr x6, [x0, #336]
	ldr x9, [x0, #304]
	sbcs x6, x6, x9
	ldr x7, [x0, #344]
	ldr x9, [x0, #312]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #288]
	str x5, [x0, #296]
	str x6, [x0, #304]
	str x7, [x0, #312]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #320]
	str x5, [x0, #328]
	str x6, [x0, #336]
	str x7, [x0, #344]
	movz w10, #0, lsl #0
	ldr x12, [x0, #128]
	ldr x13, [x0, #136]
	ldr x14, [x0, #144]
	ldr x15, [x0, #152]
	ldr x3, [x0, #192]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #200]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #208]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #216]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #352]
	str x5, [x0, #360]
	str x6, [x0, #368]
	str x7, [x0, #376]
	movz w10, #0, lsl #0
	ldr x12, [x0, #256]
	ldr x13, [x0, #264]
	ldr x14, [x0, #272]
	ldr x15, [x0, #280]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #384]
	str x5, [x0, #392]
	str x6, [x0, #400]
	str x7, [x0, #408]
	movz w10, #0, lsl #0
	ldr x12, [x0, #128]
	ldr x13, [x0, #136]
	ldr x14, [x0, #144]
	ldr x15, [x0, #152]
	ldr x3, [x0, #224]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x16, x10
	ldr x3, [x0, #232]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adcs x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	ldr x3, [x0, #240]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adcs x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	ldr x3, [x0, #248]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adcs x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adcs x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adcs x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adcs x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x10
	str x4, [x0, #416]
	str x5, [x0, #424]
	str x6, [x0, #432]
	str x7, [x0, #440]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #320]
	ldr x9, [x0, #352]
	subs x4, x4, x9
	ldr x5, [x0, #328]
	ldr x9, [x0, #360]
	sbcs x5, x5, x9
	ldr x6, [x0, #336]
	ldr x9, [x0, #368]
	sbcs x6, x6, x9
	ldr x7, [x0, #344]
	ldr x9, [x0, #376]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x6, [x0, #752]
	ldr x7, [x0, #760]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 247f
	movz w8, #0, lsl #0
	b 248f
247:
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #384]
	ldr x9, [x0, #416]
	subs x4, x4, x9
	ldr x5, [x0, #392]
	ldr x9, [x0, #424]
	sbcs x5, x5, x9
	ldr x6, [x0, #400]
	ldr x9, [x0, #432]
	sbcs x6, x6, x9
	ldr x7, [x0, #408]
	ldr x9, [x0, #440]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #736]
	str x5, [x0, #744]
	str x6, [x0, #752]
	str x7, [x0, #760]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x6, [x0, #752]
	ldr x7, [x0, #760]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	orr x8, x4, x5
	orr x8, x8, x6
	orr x8, x8, x7
	cbz x8, 249f
	movz w8, #0, lsl #0
	b 250f
249:
	movz w8, #1, lsl #0
250:
248:
229:
21:
	add x2, x0, #0
	add x0, x8, #0
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	ret
	.p2align 6

vg_ed25519_sign_expanded:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x1, [sp, #264]
	add x1, x1, #0
	add x15, sp, #192
	ldr x9, [x1, #0]
	str x9, [x15, #0]
	ldr x9, [x1, #8]
	str x9, [x15, #8]
	ldr x9, [x1, #16]
	str x9, [x15, #16]
	ldr x9, [x1, #24]
	str x9, [x15, #24]
	ldr x9, [x1, #32]
	str x9, [x15, #32]
	ldr x9, [x1, #40]
	str x9, [x15, #40]
	ldr x9, [x1, #48]
	str x9, [x15, #48]
	ldr x9, [x1, #56]
	str x9, [x15, #56]
	ldr x9, [sp, #192]
	movz x10, #65528, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #200]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #208]
	add x15, sp, #48
	str x9, [x15, #0]
	ldr x9, [sp, #216]
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #16383, lsl #48
	and x9, x9, x10
	movz x10, #16384, lsl #48
	orr x9, x9, x10
	add x15, sp, #56
	str x9, [x15, #0]
	ldr x0, [sp, #224]
	add x15, sp, #64
	str x0, [x15, #0]
	ldr x0, [sp, #232]
	add x15, sp, #64
	str x0, [x15, #8]
	ldr x0, [sp, #240]
	add x15, sp, #64
	str x0, [x15, #16]
	ldr x0, [sp, #248]
	add x15, sp, #64
	str x0, [x15, #24]
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	add x2, sp, #64
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #32
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #96
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #96
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #32
	add x1, sp, #96
	add x2, sp, #128
	add x3, sp, #32
	ldr x4, [sp, #296]
	add x4, x4, #0
	bl {vg_ed25519_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #32]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #40]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #48]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #64]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #72]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #80]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #88]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #96]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #104]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #112]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #120]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #128]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #136]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #144]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #152]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #200]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #208]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #216]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #224]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #232]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #240]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #248]
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ed25519_verify:
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x0, [sp, #288]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #264]
	add x2, x2, #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #288]
	add x0, x0, #0
	ldr x1, [sp, #272]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #288]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #288]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #280]
	add x1, x1, #0
	add x2, sp, #128
	ldr x3, [sp, #288]
	add x3, x3, #0
	bl {vg_ed25519_verify_equation}
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ed25519_sign_expanded_sha3:
	.arch_extension sha3
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x1, [sp, #264]
	add x1, x1, #0
	add x15, sp, #192
	ldr x9, [x1, #0]
	str x9, [x15, #0]
	ldr x9, [x1, #8]
	str x9, [x15, #8]
	ldr x9, [x1, #16]
	str x9, [x15, #16]
	ldr x9, [x1, #24]
	str x9, [x15, #24]
	ldr x9, [x1, #32]
	str x9, [x15, #32]
	ldr x9, [x1, #40]
	str x9, [x15, #40]
	ldr x9, [x1, #48]
	str x9, [x15, #48]
	ldr x9, [x1, #56]
	str x9, [x15, #56]
	ldr x9, [sp, #192]
	movz x10, #65528, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	and x9, x9, x10
	add x15, sp, #32
	str x9, [x15, #0]
	ldr x9, [sp, #200]
	add x15, sp, #40
	str x9, [x15, #0]
	ldr x9, [sp, #208]
	add x15, sp, #48
	str x9, [x15, #0]
	ldr x9, [sp, #216]
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #16383, lsl #48
	and x9, x9, x10
	movz x10, #16384, lsl #48
	orr x9, x9, x10
	add x15, sp, #56
	str x9, [x15, #0]
	ldr x0, [sp, #224]
	add x15, sp, #64
	str x0, [x15, #0]
	ldr x0, [sp, #232]
	add x15, sp, #64
	str x0, [x15, #8]
	ldr x0, [sp, #240]
	add x15, sp, #64
	str x0, [x15, #16]
	ldr x0, [sp, #248]
	add x15, sp, #64
	str x0, [x15, #24]
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	add x2, sp, #64
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #32
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
	add x0, sp, #96
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #0
	add x1, sp, #96
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_base}
	ldr x0, [sp, #296]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #272]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	ldr x3, [sp, #288]
	add x3, x3, #0
	ldr x4, [sp, #296]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #296]
	add x0, x0, #0
	ldr x1, [sp, #288]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #296]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #296]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	ldr x0, [sp, #256]
	add x0, x0, #32
	add x1, sp, #96
	add x2, sp, #128
	add x3, sp, #32
	ldr x4, [sp, #296]
	add x4, x4, #0
	bl {vg_ed25519_scalar_mul_add}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #32]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #40]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #48]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #56]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #64]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #72]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #80]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #88]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #96]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #104]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #112]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #120]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #128]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #136]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #144]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #152]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #192]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #200]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #208]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #216]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #224]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #232]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #240]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #248]
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6

vg_ed25519_verify_sha3:
	.arch_extension sha3
	str x30, [sp, #-16]!
	sub sp, sp, #320
	add x15, sp, #256
	str x0, [x15, #0]
	add x15, sp, #264
	str x1, [x15, #0]
	add x15, sp, #272
	str x2, [x15, #0]
	add x15, sp, #280
	str x3, [x15, #0]
	add x15, sp, #288
	str x4, [x15, #0]
	add x15, sp, #296
	str x5, [x15, #0]
	ldr x0, [sp, #288]
	add x0, x0, #0
	bl {vg_sha512_init}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #280]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #32, lsl #0
	ldr x2, [sp, #256]
	add x2, x2, #0
	movz x3, #32, lsl #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #264]
	add x2, x2, #0
	ldr x3, [sp, #272]
	add x3, x3, #0
	ldr x4, [sp, #288]
	add x4, x4, #192
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #288]
	add x0, x0, #0
	ldr x1, [sp, #272]
	add x1, x1, #64
	add x2, sp, #192
	ldr x3, [sp, #288]
	add x3, x3, #192
	bl {vg_sha512_finalize_scratch_sha3}
	add x0, sp, #128
	add x1, sp, #192
	ldr x2, [sp, #288]
	add x2, x2, #0
	bl {vg_ed25519_scalar_reduce}
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #160]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #168]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #176]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #184]
	ldr x0, [sp, #256]
	add x0, x0, #0
	ldr x1, [sp, #280]
	add x1, x1, #0
	add x2, sp, #128
	ldr x3, [sp, #288]
	add x3, x3, #0
	bl {vg_ed25519_verify_equation}
	add sp, sp, #320
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6
