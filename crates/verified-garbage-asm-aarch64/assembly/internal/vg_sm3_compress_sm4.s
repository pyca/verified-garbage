// The functions of `src/internal/vg_sm3_compress_sm4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_compress_sm4:
	cbz x2, 20f
	ldr q5, [x0, #0]
	ldr q6, [x0, #16]
	rev64 v5.4s, v5.4s
	ext v5.16b, v5.16b, v5.16b, #8
	rev64 v6.4s, v6.4s
	ext v6.16b, v6.16b, v6.16b, #8
22:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q2, [x1, #32]
	ldr q3, [x1, #48]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	rev32 v2.16b, v2.16b
	rev32 v3.16b, v3.16b
	mov v21.16b, v5.16b
	mov v22.16b, v6.16b
	movz w4, #17689, lsl #0
	movk w4, #31180, lsl #16
	dup v17.4s, w4
	ext v4.16b, v1.16b, v2.16b, #12
	ext v19.16b, v0.16b, v1.16b, #12
	ext v20.16b, v2.16b, v3.16b, #8
	sm3partw1 v4.4s, v0.4s, v3.4s
	sm3partw2 v4.4s, v20.4s, v19.4s
	eor v16.16b, v0.16b, v1.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[0]
	sm3tt2a v6.4s, v7.4s, v0.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[1]
	sm3tt2a v6.4s, v7.4s, v0.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[2]
	sm3tt2a v6.4s, v7.4s, v0.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[3]
	sm3tt2a v6.4s, v7.4s, v0.s[3]
	ext v0.16b, v2.16b, v3.16b, #12
	ext v19.16b, v1.16b, v2.16b, #12
	ext v20.16b, v3.16b, v4.16b, #8
	sm3partw1 v0.4s, v1.4s, v4.4s
	sm3partw2 v0.4s, v20.4s, v19.4s
	eor v16.16b, v1.16b, v2.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[0]
	sm3tt2a v6.4s, v7.4s, v1.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[1]
	sm3tt2a v6.4s, v7.4s, v1.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[2]
	sm3tt2a v6.4s, v7.4s, v1.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[3]
	sm3tt2a v6.4s, v7.4s, v1.s[3]
	ext v1.16b, v3.16b, v4.16b, #12
	ext v19.16b, v2.16b, v3.16b, #12
	ext v20.16b, v4.16b, v0.16b, #8
	sm3partw1 v1.4s, v2.4s, v0.4s
	sm3partw2 v1.4s, v20.4s, v19.4s
	eor v16.16b, v2.16b, v3.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[0]
	sm3tt2a v6.4s, v7.4s, v2.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[1]
	sm3tt2a v6.4s, v7.4s, v2.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[2]
	sm3tt2a v6.4s, v7.4s, v2.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[3]
	sm3tt2a v6.4s, v7.4s, v2.s[3]
	ext v2.16b, v4.16b, v0.16b, #12
	ext v19.16b, v3.16b, v4.16b, #12
	ext v20.16b, v0.16b, v1.16b, #8
	sm3partw1 v2.4s, v3.4s, v1.4s
	sm3partw2 v2.4s, v20.4s, v19.4s
	eor v16.16b, v3.16b, v4.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[0]
	sm3tt2a v6.4s, v7.4s, v3.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[1]
	sm3tt2a v6.4s, v7.4s, v3.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[2]
	sm3tt2a v6.4s, v7.4s, v3.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1a v5.4s, v7.4s, v16.s[3]
	sm3tt2a v6.4s, v7.4s, v3.s[3]
	movz w4, #31367, lsl #0
	movk w4, #40330, lsl #16
	dup v17.4s, w4
	ext v3.16b, v0.16b, v1.16b, #12
	ext v19.16b, v4.16b, v0.16b, #12
	ext v20.16b, v1.16b, v2.16b, #8
	sm3partw1 v3.4s, v4.4s, v2.4s
	sm3partw2 v3.4s, v20.4s, v19.4s
	eor v16.16b, v4.16b, v0.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v4.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v4.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v4.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v4.s[3]
	ext v4.16b, v1.16b, v2.16b, #12
	ext v19.16b, v0.16b, v1.16b, #12
	ext v20.16b, v2.16b, v3.16b, #8
	sm3partw1 v4.4s, v0.4s, v3.4s
	sm3partw2 v4.4s, v20.4s, v19.4s
	eor v16.16b, v0.16b, v1.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v0.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v0.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v0.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v0.s[3]
	ext v0.16b, v2.16b, v3.16b, #12
	ext v19.16b, v1.16b, v2.16b, #12
	ext v20.16b, v3.16b, v4.16b, #8
	sm3partw1 v0.4s, v1.4s, v4.4s
	sm3partw2 v0.4s, v20.4s, v19.4s
	eor v16.16b, v1.16b, v2.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v1.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v1.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v1.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v1.s[3]
	ext v1.16b, v3.16b, v4.16b, #12
	ext v19.16b, v2.16b, v3.16b, #12
	ext v20.16b, v4.16b, v0.16b, #8
	sm3partw1 v1.4s, v2.4s, v0.4s
	sm3partw2 v1.4s, v20.4s, v19.4s
	eor v16.16b, v2.16b, v3.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v2.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v2.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v2.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v2.s[3]
	ext v2.16b, v4.16b, v0.16b, #12
	ext v19.16b, v3.16b, v4.16b, #12
	ext v20.16b, v0.16b, v1.16b, #8
	sm3partw1 v2.4s, v3.4s, v1.4s
	sm3partw2 v2.4s, v20.4s, v19.4s
	eor v16.16b, v3.16b, v4.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v3.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v3.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v3.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v3.s[3]
	ext v3.16b, v0.16b, v1.16b, #12
	ext v19.16b, v4.16b, v0.16b, #12
	ext v20.16b, v1.16b, v2.16b, #8
	sm3partw1 v3.4s, v4.4s, v2.4s
	sm3partw2 v3.4s, v20.4s, v19.4s
	eor v16.16b, v4.16b, v0.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v4.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v4.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v4.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v4.s[3]
	ext v4.16b, v1.16b, v2.16b, #12
	ext v19.16b, v0.16b, v1.16b, #12
	ext v20.16b, v2.16b, v3.16b, #8
	sm3partw1 v4.4s, v0.4s, v3.4s
	sm3partw2 v4.4s, v20.4s, v19.4s
	eor v16.16b, v0.16b, v1.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v0.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v0.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v0.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v0.s[3]
	ext v0.16b, v2.16b, v3.16b, #12
	ext v19.16b, v1.16b, v2.16b, #12
	ext v20.16b, v3.16b, v4.16b, #8
	sm3partw1 v0.4s, v1.4s, v4.4s
	sm3partw2 v0.4s, v20.4s, v19.4s
	eor v16.16b, v1.16b, v2.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v1.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v1.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v1.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v1.s[3]
	ext v1.16b, v3.16b, v4.16b, #12
	ext v19.16b, v2.16b, v3.16b, #12
	ext v20.16b, v4.16b, v0.16b, #8
	sm3partw1 v1.4s, v2.4s, v0.4s
	sm3partw2 v1.4s, v20.4s, v19.4s
	eor v16.16b, v2.16b, v3.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v2.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v2.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v2.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v2.s[3]
	eor v16.16b, v3.16b, v4.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v3.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v3.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v3.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v3.s[3]
	eor v16.16b, v4.16b, v0.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v4.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v4.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v4.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v4.s[3]
	eor v16.16b, v0.16b, v1.16b
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[0]
	sm3tt2b v6.4s, v7.4s, v0.s[0]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[1]
	sm3tt2b v6.4s, v7.4s, v0.s[1]
	sm3ss1 v7.4s, v5.4s, v17.4s, v6.4s
	shl v18.4s, v17.4s, #1
	sri v18.4s, v17.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[2]
	sm3tt2b v6.4s, v7.4s, v0.s[2]
	sm3ss1 v7.4s, v5.4s, v18.4s, v6.4s
	shl v17.4s, v18.4s, #1
	sri v17.4s, v18.4s, #31
	sm3tt1b v5.4s, v7.4s, v16.s[3]
	sm3tt2b v6.4s, v7.4s, v0.s[3]
	eor v5.16b, v5.16b, v21.16b
	eor v6.16b, v6.16b, v22.16b
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	rev64 v5.4s, v5.4s
	ext v5.16b, v5.16b, v5.16b, #8
	rev64 v6.4s, v6.4s
	ext v6.16b, v6.16b, v6.16b, #8
	str q5, [x0, #0]
	str q6, [x0, #16]
	b 21f
20:
21:
	ret
	.p2align 6
