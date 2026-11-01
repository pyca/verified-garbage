// The functions of `src/internal/vg_sha256_compress_sha2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress_sha2:
	.arch_extension sha2
	cbz x2, 20f
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	mov v30.16b, v0.16b
	mov v31.16b, v1.16b
	adrp x4, {VG_SHA256_K}
	add x4, x4, {VG_SHA256_K}
	ldr q16, [x4, #0]
	ldr q17, [x4, #16]
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	ldr q18, [x4, #32]
	add v3.4s, v16.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	ldr q19, [x4, #48]
	add v3.4s, v17.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	ldr q20, [x4, #64]
	add v3.4s, v18.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	ldr q21, [x4, #80]
	add v3.4s, v19.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	ldr q22, [x4, #96]
	add v3.4s, v20.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	ldr q23, [x4, #112]
	add v3.4s, v21.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q24, [x4, #128]
	add v3.4s, v22.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q25, [x4, #144]
	add v3.4s, v23.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	ldr q26, [x4, #160]
	add v3.4s, v24.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	ldr q27, [x4, #176]
	add v3.4s, v25.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q28, [x4, #192]
	add v3.4s, v26.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q29, [x4, #208]
	add v3.4s, v27.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v28.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v29.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q3, [x4, #224]
	add v3.4s, v3.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q3, [x4, #240]
	add v3.4s, v3.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	add v0.4s, v0.4s, v30.4s
	add v1.4s, v1.4s, v31.4s
	add x1, x1, #64
	sub x2, x2, #1
	cbz x2, 22f
	.p2align 6
24:
	mov v30.16b, v0.16b
	mov v31.16b, v1.16b
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	add v3.4s, v16.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	add v3.4s, v17.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	add v3.4s, v18.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	add v3.4s, v19.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v20.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v21.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	add v3.4s, v22.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	add v3.4s, v23.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v24.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v25.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	add v3.4s, v26.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	add v3.4s, v27.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v28.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v29.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q3, [x4, #224]
	add v3.4s, v3.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q3, [x4, #240]
	add v3.4s, v3.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	add v0.4s, v0.4s, v30.4s
	add v1.4s, v1.4s, v31.4s
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 24b
	b 23f
22:
23:
	str q0, [x0, #0]
	str q1, [x0, #16]
	b 21f
20:
21:
	ret
	.arch_extension nosha2
	.p2align 6
