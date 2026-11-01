// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
20:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	str q0, [x1, #0]
	str q1, [x1, #16]
	add x0, x0, #12
	add x1, x1, #32
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6
