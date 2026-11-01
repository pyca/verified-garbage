// The functions of `src/internal/vg_mldsa_montgomery_dot7.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_montgomery_dot7:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz w10, #57343, lsl #0
	movk w10, #64639, lsl #16
	dup v16.4s, w9
	dup v17.4s, w10
	movz x12, #64, lsl #0
20:
	ldr q0, [x1, #0]
	ldr q1, [x2, #0]
	umull v2.2d, v0.2s, v1.2s
	umull2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #1024]
	ldr q1, [x2, #1024]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #2048]
	ldr q1, [x2, #2048]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #3072]
	ldr q1, [x2, #3072]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #4096]
	ldr q1, [x2, #4096]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #5120]
	ldr q1, [x2, #5120]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	ldr q0, [x1, #6144]
	ldr q1, [x2, #6144]
	umlal v2.2d, v0.2s, v1.2s
	umlal2 v3.2d, v0.4s, v1.4s
	uzp1 v4.4s, v2.4s, v3.4s
	mul v4.4s, v4.4s, v17.4s
	umlal v2.2d, v4.2s, v16.2s
	umlal2 v3.2d, v4.4s, v16.4s
	uzp2 v0.4s, v2.4s, v3.4s
	sub v4.4s, v0.4s, v16.4s
	umin v0.4s, v0.4s, v4.4s
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	add x2, x2, #16
	sub x12, x12, #1
	cbnz x12, 20b
	ret
	.p2align 6
