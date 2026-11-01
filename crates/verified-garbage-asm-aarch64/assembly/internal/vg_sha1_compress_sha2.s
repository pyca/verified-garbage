// The functions of `src/internal/vg_sha1_compress_sha2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress_sha2:
	.arch_extension sha2
	cbz x2, 20f
	movz w4, #31129, lsl #0
	movk w4, #23170, lsl #16
	dup v18.4s, w4
	movz w4, #60321, lsl #0
	movk w4, #28377, lsl #16
	dup v19.4s, w4
	movz w4, #48348, lsl #0
	movk w4, #36635, lsl #16
	dup v20.4s, w4
	movz w4, #49622, lsl #0
	movk w4, #51810, lsl #16
	dup v21.4s, w4
	ldr q0, [x0, #0]
	ldr w4, [x0, #16]
	dup v1.4s, w4
	dup s1, v1.s[0]
22:
	mov v16.16b, v0.16b
	mov v17.16b, v1.16b
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	add v3.4s, v18.4s, v4.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	add v3.4s, v18.4s, v5.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	add v3.4s, v18.4s, v6.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	add v3.4s, v18.4s, v7.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v18.4s, v4.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v19.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v19.4s, v6.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v19.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v19.4s, v4.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v19.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v20.4s, v6.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v20.4s, v7.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v20.4s, v4.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v20.4s, v5.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v20.4s, v6.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v21.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v21.4s, v4.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v21.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v21.4s, v6.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v21.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	add v0.4s, v0.4s, v16.4s
	add v1.4s, v1.4s, v17.4s
	str q0, [x0, #0]
	umov w4, v1.s[0]
	str w4, [x0, #16]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.arch_extension nosha2
	.p2align 6
