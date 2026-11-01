// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movz x11, #32, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #32
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6
