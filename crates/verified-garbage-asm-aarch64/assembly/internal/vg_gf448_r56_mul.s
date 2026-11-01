// The functions of `src/internal/vg_gf448_r56_mul.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r56_mul:
	mov v21.d[0], x30
	mov v21.d[1], x21
	mov v22.d[0], x22
	mov v22.d[1], x23
	mov v23.d[0], x24
	mov v23.d[1], x25
	mov v24.d[0], x26
	mov v24.d[1], x27
	mov v25.d[0], x28
	add x10, x0, x2
	add x30, x0, x3
	add x1, x0, x1
	add x3, x0, #0
	movz x12, #65535, lsl #0
	movk x12, #4095, lsl #16
	ldr x0, [x10, #0]
	ldr x2, [x10, #8]
	ldr x4, [x10, #16]
	ldr x5, [x10, #24]
	ldr x6, [x10, #32]
	ldr x7, [x10, #40]
	ldr x8, [x10, #48]
	ldr x9, [x10, #56]
	movz x25, #65535, lsl #0
	movk x25, #65535, lsl #16
	movk x25, #65535, lsl #32
	movk x25, #255, lsl #48
	movz x26, #0, lsl #0
	add x13, x0, x6
	str x13, [x3, #3584]
	ldr x10, [x30, #0]
	ldr x11, [x30, #32]
	add x10, x10, x11
	str x10, [x3, #3616]
	add x13, x2, x7
	str x13, [x3, #3592]
	ldr x10, [x30, #8]
	ldr x11, [x30, #40]
	add x10, x10, x11
	str x10, [x3, #3624]
	add x13, x4, x8
	str x13, [x3, #3600]
	ldr x10, [x30, #16]
	ldr x11, [x30, #48]
	add x10, x10, x11
	str x10, [x3, #3632]
	add x13, x5, x9
	str x13, [x3, #3608]
	ldr x10, [x30, #24]
	ldr x11, [x30, #56]
	add x10, x10, x11
	str x10, [x3, #3640]
	ldr x11, [x30, #32]
	mul x14, x6, x11
	umulh x15, x6, x11
	ldr x11, [x30, #56]
	mul x16, x7, x11
	umulh x17, x7, x11
	ldr x11, [x30, #48]
	mul x10, x8, x11
	umulh x11, x8, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x11, [x30, #40]
	mul x10, x9, x11
	umulh x11, x9, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3584]
	ldr x11, [x3, #3616]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3592]
	ldr x11, [x3, #3640]
	mul x27, x13, x11
	umulh x28, x13, x11
	ldr x13, [x3, #3600]
	ldr x11, [x3, #3632]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x27, x27, x10
	adc x28, x28, x11
	ldr x13, [x3, #3608]
	ldr x11, [x3, #3624]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x27, x27, x10
	adc x28, x28, x11
	adds x14, x14, x27
	adc x15, x15, x28
	adds x16, x16, x27
	adc x17, x17, x28
	ldr x11, [x30, #0]
	mul x10, x0, x11
	umulh x11, x0, x11
	adds x14, x14, x10
	adc x15, x15, x11
	subs x16, x16, x10
	sbc x17, x17, x11
	ldr x11, [x30, #24]
	mul x10, x2, x11
	umulh x11, x2, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	ldr x11, [x30, #16]
	mul x10, x4, x11
	umulh x11, x4, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	ldr x11, [x30, #8]
	mul x10, x5, x11
	umulh x11, x5, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	and x10, x14, x25
	str x10, [x1, #0]
	extr x23, x15, x14, #56
	and x10, x16, x25
	str x10, [x1, #32]
	extr x24, x17, x16, #56
	ldr x11, [x30, #40]
	mul x14, x6, x11
	umulh x15, x6, x11
	ldr x11, [x30, #32]
	mul x10, x7, x11
	umulh x11, x7, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x11, [x30, #56]
	mul x16, x8, x11
	umulh x17, x8, x11
	ldr x11, [x30, #48]
	mul x10, x9, x11
	umulh x11, x9, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3584]
	ldr x11, [x3, #3624]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3592]
	ldr x11, [x3, #3616]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3600]
	ldr x11, [x3, #3640]
	mul x27, x13, x11
	umulh x28, x13, x11
	ldr x13, [x3, #3608]
	ldr x11, [x3, #3632]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x27, x27, x10
	adc x28, x28, x11
	adds x14, x14, x27
	adc x15, x15, x28
	adds x16, x16, x27
	adc x17, x17, x28
	ldr x11, [x30, #8]
	mul x21, x0, x11
	umulh x22, x0, x11
	ldr x11, [x30, #0]
	mul x10, x2, x11
	umulh x11, x2, x11
	adds x21, x21, x10
	adc x22, x22, x11
	adds x14, x14, x21
	adc x15, x15, x22
	subs x16, x16, x21
	sbc x17, x17, x22
	ldr x11, [x30, #24]
	mul x10, x4, x11
	umulh x11, x4, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	ldr x11, [x30, #16]
	mul x10, x5, x11
	umulh x11, x5, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	adds x14, x14, x23
	adc x15, x15, x26
	and x10, x14, x25
	str x10, [x1, #8]
	extr x23, x15, x14, #56
	adds x16, x16, x24
	adc x17, x17, x26
	and x10, x16, x25
	str x10, [x1, #40]
	extr x24, x17, x16, #56
	ldr x11, [x30, #48]
	mul x14, x6, x11
	umulh x15, x6, x11
	ldr x11, [x30, #40]
	mul x10, x7, x11
	umulh x11, x7, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x11, [x30, #32]
	mul x10, x8, x11
	umulh x11, x8, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x11, [x30, #56]
	mul x16, x9, x11
	umulh x17, x9, x11
	ldr x13, [x3, #3584]
	ldr x11, [x3, #3632]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3592]
	ldr x11, [x3, #3624]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3600]
	ldr x11, [x3, #3616]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3608]
	ldr x11, [x3, #3640]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x14, x14, x10
	adc x15, x15, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x11, [x30, #16]
	mul x21, x0, x11
	umulh x22, x0, x11
	ldr x11, [x30, #8]
	mul x10, x2, x11
	umulh x11, x2, x11
	adds x21, x21, x10
	adc x22, x22, x11
	ldr x11, [x30, #0]
	mul x10, x4, x11
	umulh x11, x4, x11
	adds x21, x21, x10
	adc x22, x22, x11
	adds x14, x14, x21
	adc x15, x15, x22
	subs x16, x16, x21
	sbc x17, x17, x22
	ldr x11, [x30, #24]
	mul x10, x5, x11
	umulh x11, x5, x11
	subs x14, x14, x10
	sbc x15, x15, x11
	adds x14, x14, x23
	adc x15, x15, x26
	and x10, x14, x25
	str x10, [x1, #16]
	extr x23, x15, x14, #56
	adds x16, x16, x24
	adc x17, x17, x26
	and x10, x16, x25
	str x10, [x1, #48]
	extr x24, x17, x16, #56
	ldr x11, [x30, #56]
	mul x14, x6, x11
	umulh x15, x6, x11
	ldr x11, [x30, #48]
	mul x10, x7, x11
	umulh x11, x7, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x11, [x30, #40]
	mul x10, x8, x11
	umulh x11, x8, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x11, [x30, #32]
	mul x10, x9, x11
	umulh x11, x9, x11
	adds x14, x14, x10
	adc x15, x15, x11
	ldr x13, [x3, #3584]
	ldr x11, [x3, #3640]
	mul x16, x13, x11
	umulh x17, x13, x11
	ldr x13, [x3, #3592]
	ldr x11, [x3, #3632]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3600]
	ldr x11, [x3, #3624]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x13, [x3, #3608]
	ldr x11, [x3, #3616]
	mul x10, x13, x11
	umulh x11, x13, x11
	adds x16, x16, x10
	adc x17, x17, x11
	ldr x11, [x30, #24]
	mul x21, x0, x11
	umulh x22, x0, x11
	ldr x11, [x30, #16]
	mul x10, x2, x11
	umulh x11, x2, x11
	adds x21, x21, x10
	adc x22, x22, x11
	ldr x11, [x30, #8]
	mul x10, x4, x11
	umulh x11, x4, x11
	adds x21, x21, x10
	adc x22, x22, x11
	ldr x11, [x30, #0]
	mul x10, x5, x11
	umulh x11, x5, x11
	adds x21, x21, x10
	adc x22, x22, x11
	adds x14, x14, x21
	adc x15, x15, x22
	subs x16, x16, x21
	sbc x17, x17, x22
	adds x14, x14, x23
	adc x15, x15, x26
	and x10, x14, x25
	str x10, [x1, #24]
	extr x23, x15, x14, #56
	adds x16, x16, x24
	adc x17, x17, x26
	and x10, x16, x25
	str x10, [x1, #56]
	extr x24, x17, x16, #56
	ldr x4, [x1, #0]
	ldr x5, [x1, #8]
	ldr x6, [x1, #32]
	ldr x7, [x1, #40]
	add x4, x4, x24
	add x6, x6, x24
	add x6, x6, x23
	lsr x8, x4, #56
	and x4, x4, x25
	add x5, x5, x8
	lsr x8, x6, #56
	and x6, x6, x25
	add x7, x7, x8
	str x4, [x1, #0]
	str x5, [x1, #8]
	str x6, [x1, #32]
	str x7, [x1, #40]
	umov x30, v21.d[0]
	umov x21, v21.d[1]
	umov x22, v22.d[0]
	umov x23, v22.d[1]
	umov x24, v23.d[0]
	umov x25, v23.d[1]
	umov x26, v24.d[0]
	umov x27, v24.d[1]
	umov x28, v25.d[0]
	ret
	.p2align 6
