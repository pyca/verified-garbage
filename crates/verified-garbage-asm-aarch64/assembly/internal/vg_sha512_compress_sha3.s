// The functions of `src/internal/vg_sha512_compress_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress_sha3:
	.arch_extension sha3
	cbz x2, 20f
	adrp x4, {VG_SHA512_K}
	add x4, x4, {VG_SHA512_K}
	ldr q29, [x4, #0]
	ldr q30, [x4, #16]
	movi v31.2d, #0
	ldr q24, [x0, #0]
	ldr q25, [x0, #16]
	ldr q26, [x0, #32]
	ldr q27, [x0, #48]
22:
	mov v0.16b, v24.16b
	mov v1.16b, v25.16b
	mov v2.16b, v26.16b
	mov v3.16b, v27.16b
	ldr q16, [x1, #0]
	rev64 v16.16b, v16.16b
	add v4.2d, v29.2d, v16.2d
	ldr q29, [x4, #32]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ldr q17, [x1, #16]
	rev64 v17.16b, v17.16b
	add v1.2d, v30.2d, v17.2d
	ldr q30, [x4, #48]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ldr q18, [x1, #32]
	rev64 v18.16b, v18.16b
	add v0.2d, v29.2d, v18.2d
	ldr q29, [x4, #64]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ldr q19, [x1, #48]
	rev64 v19.16b, v19.16b
	add v4.2d, v30.2d, v19.2d
	ldr q30, [x4, #80]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ldr q20, [x1, #64]
	rev64 v20.16b, v20.16b
	add v1.2d, v29.2d, v20.2d
	ldr q29, [x4, #96]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ldr q21, [x1, #80]
	rev64 v21.16b, v21.16b
	add v0.2d, v30.2d, v21.2d
	ldr q30, [x4, #112]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ldr q22, [x1, #96]
	rev64 v22.16b, v22.16b
	add v4.2d, v29.2d, v22.2d
	ldr q29, [x4, #128]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ldr q23, [x1, #112]
	rev64 v23.16b, v23.16b
	add v1.2d, v30.2d, v23.2d
	ldr q30, [x4, #144]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v20.16b, v21.16b, #8
	sha512su0 v16.2d, v17.2d
	sha512su1 v16.2d, v23.2d, v6.2d
	add v0.2d, v29.2d, v16.2d
	ldr q29, [x4, #160]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v21.16b, v22.16b, #8
	sha512su0 v17.2d, v18.2d
	sha512su1 v17.2d, v16.2d, v6.2d
	add v4.2d, v30.2d, v17.2d
	ldr q30, [x4, #176]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v22.16b, v23.16b, #8
	sha512su0 v18.2d, v19.2d
	sha512su1 v18.2d, v17.2d, v6.2d
	add v1.2d, v29.2d, v18.2d
	ldr q29, [x4, #192]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v23.16b, v16.16b, #8
	sha512su0 v19.2d, v20.2d
	sha512su1 v19.2d, v18.2d, v6.2d
	add v0.2d, v30.2d, v19.2d
	ldr q30, [x4, #208]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v16.16b, v17.16b, #8
	sha512su0 v20.2d, v21.2d
	sha512su1 v20.2d, v19.2d, v6.2d
	add v4.2d, v29.2d, v20.2d
	ldr q29, [x4, #224]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v17.16b, v18.16b, #8
	sha512su0 v21.2d, v22.2d
	sha512su1 v21.2d, v20.2d, v6.2d
	add v1.2d, v30.2d, v21.2d
	ldr q30, [x4, #240]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v18.16b, v19.16b, #8
	sha512su0 v22.2d, v23.2d
	sha512su1 v22.2d, v21.2d, v6.2d
	add v0.2d, v29.2d, v22.2d
	ldr q29, [x4, #256]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v19.16b, v20.16b, #8
	sha512su0 v23.2d, v16.2d
	sha512su1 v23.2d, v22.2d, v6.2d
	add v4.2d, v30.2d, v23.2d
	ldr q30, [x4, #272]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v20.16b, v21.16b, #8
	sha512su0 v16.2d, v17.2d
	sha512su1 v16.2d, v23.2d, v6.2d
	add v1.2d, v29.2d, v16.2d
	ldr q29, [x4, #288]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v21.16b, v22.16b, #8
	sha512su0 v17.2d, v18.2d
	sha512su1 v17.2d, v16.2d, v6.2d
	add v0.2d, v30.2d, v17.2d
	ldr q30, [x4, #304]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v22.16b, v23.16b, #8
	sha512su0 v18.2d, v19.2d
	sha512su1 v18.2d, v17.2d, v6.2d
	add v4.2d, v29.2d, v18.2d
	ldr q29, [x4, #320]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v23.16b, v16.16b, #8
	sha512su0 v19.2d, v20.2d
	sha512su1 v19.2d, v18.2d, v6.2d
	add v1.2d, v30.2d, v19.2d
	ldr q30, [x4, #336]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v16.16b, v17.16b, #8
	sha512su0 v20.2d, v21.2d
	sha512su1 v20.2d, v19.2d, v6.2d
	add v0.2d, v29.2d, v20.2d
	ldr q29, [x4, #352]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v17.16b, v18.16b, #8
	sha512su0 v21.2d, v22.2d
	sha512su1 v21.2d, v20.2d, v6.2d
	add v4.2d, v30.2d, v21.2d
	ldr q30, [x4, #368]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v18.16b, v19.16b, #8
	sha512su0 v22.2d, v23.2d
	sha512su1 v22.2d, v21.2d, v6.2d
	add v1.2d, v29.2d, v22.2d
	ldr q29, [x4, #384]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v19.16b, v20.16b, #8
	sha512su0 v23.2d, v16.2d
	sha512su1 v23.2d, v22.2d, v6.2d
	add v0.2d, v30.2d, v23.2d
	ldr q30, [x4, #400]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v20.16b, v21.16b, #8
	sha512su0 v16.2d, v17.2d
	sha512su1 v16.2d, v23.2d, v6.2d
	add v4.2d, v29.2d, v16.2d
	ldr q29, [x4, #416]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v21.16b, v22.16b, #8
	sha512su0 v17.2d, v18.2d
	sha512su1 v17.2d, v16.2d, v6.2d
	add v1.2d, v30.2d, v17.2d
	ldr q30, [x4, #432]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v22.16b, v23.16b, #8
	sha512su0 v18.2d, v19.2d
	sha512su1 v18.2d, v17.2d, v6.2d
	add v0.2d, v29.2d, v18.2d
	ldr q29, [x4, #448]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v23.16b, v16.16b, #8
	sha512su0 v19.2d, v20.2d
	sha512su1 v19.2d, v18.2d, v6.2d
	add v4.2d, v30.2d, v19.2d
	ldr q30, [x4, #464]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v16.16b, v17.16b, #8
	sha512su0 v20.2d, v21.2d
	sha512su1 v20.2d, v19.2d, v6.2d
	add v1.2d, v29.2d, v20.2d
	ldr q29, [x4, #480]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v17.16b, v18.16b, #8
	sha512su0 v21.2d, v22.2d
	sha512su1 v21.2d, v20.2d, v6.2d
	add v0.2d, v30.2d, v21.2d
	ldr q30, [x4, #496]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v18.16b, v19.16b, #8
	sha512su0 v22.2d, v23.2d
	sha512su1 v22.2d, v21.2d, v6.2d
	add v4.2d, v29.2d, v22.2d
	ldr q29, [x4, #512]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v19.16b, v20.16b, #8
	sha512su0 v23.2d, v16.2d
	sha512su1 v23.2d, v22.2d, v6.2d
	add v1.2d, v30.2d, v23.2d
	ldr q30, [x4, #528]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v20.16b, v21.16b, #8
	sha512su0 v16.2d, v17.2d
	sha512su1 v16.2d, v23.2d, v6.2d
	add v0.2d, v29.2d, v16.2d
	ldr q29, [x4, #544]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v21.16b, v22.16b, #8
	sha512su0 v17.2d, v18.2d
	sha512su1 v17.2d, v16.2d, v6.2d
	add v4.2d, v30.2d, v17.2d
	ldr q30, [x4, #560]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v22.16b, v23.16b, #8
	sha512su0 v18.2d, v19.2d
	sha512su1 v18.2d, v17.2d, v6.2d
	add v1.2d, v29.2d, v18.2d
	ldr q29, [x4, #576]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v23.16b, v16.16b, #8
	sha512su0 v19.2d, v20.2d
	sha512su1 v19.2d, v18.2d, v6.2d
	add v0.2d, v30.2d, v19.2d
	ldr q30, [x4, #592]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v16.16b, v17.16b, #8
	sha512su0 v20.2d, v21.2d
	sha512su1 v20.2d, v19.2d, v6.2d
	add v4.2d, v29.2d, v20.2d
	ldr q29, [x4, #608]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	ext v6.16b, v17.16b, v18.16b, #8
	sha512su0 v21.2d, v22.2d
	sha512su1 v21.2d, v20.2d, v6.2d
	add v1.2d, v30.2d, v21.2d
	ldr q30, [x4, #624]
	ext v1.16b, v1.16b, v1.16b, #8
	add v1.2d, v1.2d, v2.2d
	add v3.2d, v1.2d, v0.2d
	ext v6.16b, v5.16b, v2.16b, #8
	ext v7.16b, v31.16b, v5.16b, #8
	ext v28.16b, v0.16b, v5.16b, #8
	sha512h q3, q6, v7.2d
	sha512h q1, q6, v28.2d
	sha512h2 q1, q0, v4.2d
	ext v6.16b, v18.16b, v19.16b, #8
	sha512su0 v22.2d, v23.2d
	sha512su1 v22.2d, v21.2d, v6.2d
	add v0.2d, v29.2d, v22.2d
	ldr q29, [x4, #0]
	ext v0.16b, v0.16b, v0.16b, #8
	add v0.2d, v0.2d, v5.2d
	add v2.2d, v0.2d, v4.2d
	ext v6.16b, v3.16b, v5.16b, #8
	ext v7.16b, v31.16b, v3.16b, #8
	ext v28.16b, v4.16b, v3.16b, #8
	sha512h q2, q6, v7.2d
	sha512h q0, q6, v28.2d
	sha512h2 q0, q4, v1.2d
	ext v6.16b, v19.16b, v20.16b, #8
	sha512su0 v23.2d, v16.2d
	sha512su1 v23.2d, v22.2d, v6.2d
	add v4.2d, v30.2d, v23.2d
	ldr q30, [x4, #16]
	ext v4.16b, v4.16b, v4.16b, #8
	add v4.2d, v4.2d, v3.2d
	add v5.2d, v4.2d, v1.2d
	ext v6.16b, v2.16b, v3.16b, #8
	ext v7.16b, v31.16b, v2.16b, #8
	ext v28.16b, v1.16b, v2.16b, #8
	sha512h q5, q6, v7.2d
	sha512h q4, q6, v28.2d
	sha512h2 q4, q1, v0.2d
	add v24.2d, v4.2d, v24.2d
	add v25.2d, v0.2d, v25.2d
	add v26.2d, v5.2d, v26.2d
	add v27.2d, v2.2d, v27.2d
	str q24, [x0, #0]
	str q25, [x0, #16]
	str q26, [x0, #32]
	str q27, [x0, #48]
	add x1, x1, #128
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.arch_extension nosha3
	.p2align 6
