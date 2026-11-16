// The functions of `src/internal/vg_sha256_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress:
	cbz x2, 20f
	mov v18.d[0], x19
	mov v18.d[1], x20
	mov v19.d[0], x21
	mov v19.d[1], x22
	mov v20.d[0], x23
	mov v20.d[1], x24
	mov v21.d[0], x25
	mov v21.d[1], x26
	mov v22.d[0], x27
	mov v22.d[1], x28
	mov v16.d[0], x0
	mov v16.d[1], x1
	mov v17.d[0], x2
	adrp x3, {VG_SHA256_K}
	add x3, x3, {VG_SHA256_K}
22:
	umov x0, v16.d[1]
	ldr x13, [x0, #0]
	rev x13, x13
	lsr x12, x13, #32
	ldr x15, [x0, #8]
	rev x15, x15
	lsr x14, x15, #32
	ldr x17, [x0, #16]
	rev x17, x17
	lsr x16, x17, #32
	ldr x20, [x0, #24]
	rev x20, x20
	lsr x19, x20, #32
	ldr x22, [x0, #32]
	rev x22, x22
	lsr x21, x22, #32
	ldr x24, [x0, #40]
	rev x24, x24
	lsr x23, x24, #32
	ldr x26, [x0, #48]
	rev x26, x26
	lsr x25, x26, #32
	ldr x28, [x0, #56]
	rev x28, x28
	lsr x27, x28, #32
	add x0, x0, #64
	mov v16.d[1], x0
	umov x0, v16.d[0]
	ldr w4, [x0, #0]
	ldr w5, [x0, #4]
	ldr w6, [x0, #8]
	ldr w7, [x0, #12]
	ldr w8, [x0, #16]
	ldr w9, [x0, #20]
	ldr w10, [x0, #24]
	ldr w11, [x0, #28]
	eor w2, w5, w6
	ldr w0, [x3, #0]
	add w11, w11, w12
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	ldr w0, [x3, #4]
	add w10, w10, w13
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	ldr w0, [x3, #8]
	add w9, w9, w14
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	ldr w0, [x3, #12]
	add w8, w8, w15
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	ldr w0, [x3, #16]
	add w7, w7, w16
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	ldr w0, [x3, #20]
	add w6, w6, w17
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	ldr w0, [x3, #24]
	add w5, w5, w19
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	ldr w0, [x3, #28]
	add w4, w4, w20
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	ldr w0, [x3, #32]
	add w11, w11, w21
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	ldr w0, [x3, #36]
	add w10, w10, w22
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	ldr w0, [x3, #40]
	add w9, w9, w23
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	ldr w0, [x3, #44]
	add w8, w8, w24
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	ldr w0, [x3, #48]
	add w7, w7, w25
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	ldr w0, [x3, #52]
	add w6, w6, w26
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	ldr w0, [x3, #56]
	add w5, w5, w27
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	ldr w0, [x3, #60]
	add w4, w4, w28
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w13, #3
	eor w0, w0, w13, ror #7
	eor w0, w0, w13, ror #18
	add w12, w12, w0
	lsr w0, w27, #10
	eor w0, w0, w27, ror #17
	eor w0, w0, w27, ror #19
	add w12, w12, w22
	add w12, w12, w0
	ldr w0, [x3, #64]
	add w11, w11, w12
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w14, #3
	eor w0, w0, w14, ror #7
	eor w0, w0, w14, ror #18
	add w13, w13, w0
	lsr w0, w28, #10
	eor w0, w0, w28, ror #17
	eor w0, w0, w28, ror #19
	add w13, w13, w23
	add w13, w13, w0
	ldr w0, [x3, #68]
	add w10, w10, w13
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w15, #3
	eor w0, w0, w15, ror #7
	eor w0, w0, w15, ror #18
	add w14, w14, w0
	lsr w0, w12, #10
	eor w0, w0, w12, ror #17
	eor w0, w0, w12, ror #19
	add w14, w14, w24
	add w14, w14, w0
	ldr w0, [x3, #72]
	add w9, w9, w14
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w16, #3
	eor w0, w0, w16, ror #7
	eor w0, w0, w16, ror #18
	add w15, w15, w0
	lsr w0, w13, #10
	eor w0, w0, w13, ror #17
	eor w0, w0, w13, ror #19
	add w15, w15, w25
	add w15, w15, w0
	ldr w0, [x3, #76]
	add w8, w8, w15
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w17, #3
	eor w0, w0, w17, ror #7
	eor w0, w0, w17, ror #18
	add w16, w16, w0
	lsr w0, w14, #10
	eor w0, w0, w14, ror #17
	eor w0, w0, w14, ror #19
	add w16, w16, w26
	add w16, w16, w0
	ldr w0, [x3, #80]
	add w7, w7, w16
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w19, #3
	eor w0, w0, w19, ror #7
	eor w0, w0, w19, ror #18
	add w17, w17, w0
	lsr w0, w15, #10
	eor w0, w0, w15, ror #17
	eor w0, w0, w15, ror #19
	add w17, w17, w27
	add w17, w17, w0
	ldr w0, [x3, #84]
	add w6, w6, w17
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w20, #3
	eor w0, w0, w20, ror #7
	eor w0, w0, w20, ror #18
	add w19, w19, w0
	lsr w0, w16, #10
	eor w0, w0, w16, ror #17
	eor w0, w0, w16, ror #19
	add w19, w19, w28
	add w19, w19, w0
	ldr w0, [x3, #88]
	add w5, w5, w19
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w21, #3
	eor w0, w0, w21, ror #7
	eor w0, w0, w21, ror #18
	add w20, w20, w0
	lsr w0, w17, #10
	eor w0, w0, w17, ror #17
	eor w0, w0, w17, ror #19
	add w20, w20, w12
	add w20, w20, w0
	ldr w0, [x3, #92]
	add w4, w4, w20
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w22, #3
	eor w0, w0, w22, ror #7
	eor w0, w0, w22, ror #18
	add w21, w21, w0
	lsr w0, w19, #10
	eor w0, w0, w19, ror #17
	eor w0, w0, w19, ror #19
	add w21, w21, w13
	add w21, w21, w0
	ldr w0, [x3, #96]
	add w11, w11, w21
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w23, #3
	eor w0, w0, w23, ror #7
	eor w0, w0, w23, ror #18
	add w22, w22, w0
	lsr w0, w20, #10
	eor w0, w0, w20, ror #17
	eor w0, w0, w20, ror #19
	add w22, w22, w14
	add w22, w22, w0
	ldr w0, [x3, #100]
	add w10, w10, w22
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w24, #3
	eor w0, w0, w24, ror #7
	eor w0, w0, w24, ror #18
	add w23, w23, w0
	lsr w0, w21, #10
	eor w0, w0, w21, ror #17
	eor w0, w0, w21, ror #19
	add w23, w23, w15
	add w23, w23, w0
	ldr w0, [x3, #104]
	add w9, w9, w23
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w25, #3
	eor w0, w0, w25, ror #7
	eor w0, w0, w25, ror #18
	add w24, w24, w0
	lsr w0, w22, #10
	eor w0, w0, w22, ror #17
	eor w0, w0, w22, ror #19
	add w24, w24, w16
	add w24, w24, w0
	ldr w0, [x3, #108]
	add w8, w8, w24
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w26, #3
	eor w0, w0, w26, ror #7
	eor w0, w0, w26, ror #18
	add w25, w25, w0
	lsr w0, w23, #10
	eor w0, w0, w23, ror #17
	eor w0, w0, w23, ror #19
	add w25, w25, w17
	add w25, w25, w0
	ldr w0, [x3, #112]
	add w7, w7, w25
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w27, #3
	eor w0, w0, w27, ror #7
	eor w0, w0, w27, ror #18
	add w26, w26, w0
	lsr w0, w24, #10
	eor w0, w0, w24, ror #17
	eor w0, w0, w24, ror #19
	add w26, w26, w19
	add w26, w26, w0
	ldr w0, [x3, #116]
	add w6, w6, w26
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w28, #3
	eor w0, w0, w28, ror #7
	eor w0, w0, w28, ror #18
	add w27, w27, w0
	lsr w0, w25, #10
	eor w0, w0, w25, ror #17
	eor w0, w0, w25, ror #19
	add w27, w27, w20
	add w27, w27, w0
	ldr w0, [x3, #120]
	add w5, w5, w27
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w12, #3
	eor w0, w0, w12, ror #7
	eor w0, w0, w12, ror #18
	add w28, w28, w0
	lsr w0, w26, #10
	eor w0, w0, w26, ror #17
	eor w0, w0, w26, ror #19
	add w28, w28, w21
	add w28, w28, w0
	ldr w0, [x3, #124]
	add w4, w4, w28
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w13, #3
	eor w0, w0, w13, ror #7
	eor w0, w0, w13, ror #18
	add w12, w12, w0
	lsr w0, w27, #10
	eor w0, w0, w27, ror #17
	eor w0, w0, w27, ror #19
	add w12, w12, w22
	add w12, w12, w0
	ldr w0, [x3, #128]
	add w11, w11, w12
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w14, #3
	eor w0, w0, w14, ror #7
	eor w0, w0, w14, ror #18
	add w13, w13, w0
	lsr w0, w28, #10
	eor w0, w0, w28, ror #17
	eor w0, w0, w28, ror #19
	add w13, w13, w23
	add w13, w13, w0
	ldr w0, [x3, #132]
	add w10, w10, w13
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w15, #3
	eor w0, w0, w15, ror #7
	eor w0, w0, w15, ror #18
	add w14, w14, w0
	lsr w0, w12, #10
	eor w0, w0, w12, ror #17
	eor w0, w0, w12, ror #19
	add w14, w14, w24
	add w14, w14, w0
	ldr w0, [x3, #136]
	add w9, w9, w14
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w16, #3
	eor w0, w0, w16, ror #7
	eor w0, w0, w16, ror #18
	add w15, w15, w0
	lsr w0, w13, #10
	eor w0, w0, w13, ror #17
	eor w0, w0, w13, ror #19
	add w15, w15, w25
	add w15, w15, w0
	ldr w0, [x3, #140]
	add w8, w8, w15
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w17, #3
	eor w0, w0, w17, ror #7
	eor w0, w0, w17, ror #18
	add w16, w16, w0
	lsr w0, w14, #10
	eor w0, w0, w14, ror #17
	eor w0, w0, w14, ror #19
	add w16, w16, w26
	add w16, w16, w0
	ldr w0, [x3, #144]
	add w7, w7, w16
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w19, #3
	eor w0, w0, w19, ror #7
	eor w0, w0, w19, ror #18
	add w17, w17, w0
	lsr w0, w15, #10
	eor w0, w0, w15, ror #17
	eor w0, w0, w15, ror #19
	add w17, w17, w27
	add w17, w17, w0
	ldr w0, [x3, #148]
	add w6, w6, w17
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w20, #3
	eor w0, w0, w20, ror #7
	eor w0, w0, w20, ror #18
	add w19, w19, w0
	lsr w0, w16, #10
	eor w0, w0, w16, ror #17
	eor w0, w0, w16, ror #19
	add w19, w19, w28
	add w19, w19, w0
	ldr w0, [x3, #152]
	add w5, w5, w19
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w21, #3
	eor w0, w0, w21, ror #7
	eor w0, w0, w21, ror #18
	add w20, w20, w0
	lsr w0, w17, #10
	eor w0, w0, w17, ror #17
	eor w0, w0, w17, ror #19
	add w20, w20, w12
	add w20, w20, w0
	ldr w0, [x3, #156]
	add w4, w4, w20
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w22, #3
	eor w0, w0, w22, ror #7
	eor w0, w0, w22, ror #18
	add w21, w21, w0
	lsr w0, w19, #10
	eor w0, w0, w19, ror #17
	eor w0, w0, w19, ror #19
	add w21, w21, w13
	add w21, w21, w0
	ldr w0, [x3, #160]
	add w11, w11, w21
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w23, #3
	eor w0, w0, w23, ror #7
	eor w0, w0, w23, ror #18
	add w22, w22, w0
	lsr w0, w20, #10
	eor w0, w0, w20, ror #17
	eor w0, w0, w20, ror #19
	add w22, w22, w14
	add w22, w22, w0
	ldr w0, [x3, #164]
	add w10, w10, w22
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w24, #3
	eor w0, w0, w24, ror #7
	eor w0, w0, w24, ror #18
	add w23, w23, w0
	lsr w0, w21, #10
	eor w0, w0, w21, ror #17
	eor w0, w0, w21, ror #19
	add w23, w23, w15
	add w23, w23, w0
	ldr w0, [x3, #168]
	add w9, w9, w23
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w25, #3
	eor w0, w0, w25, ror #7
	eor w0, w0, w25, ror #18
	add w24, w24, w0
	lsr w0, w22, #10
	eor w0, w0, w22, ror #17
	eor w0, w0, w22, ror #19
	add w24, w24, w16
	add w24, w24, w0
	ldr w0, [x3, #172]
	add w8, w8, w24
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w26, #3
	eor w0, w0, w26, ror #7
	eor w0, w0, w26, ror #18
	add w25, w25, w0
	lsr w0, w23, #10
	eor w0, w0, w23, ror #17
	eor w0, w0, w23, ror #19
	add w25, w25, w17
	add w25, w25, w0
	ldr w0, [x3, #176]
	add w7, w7, w25
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w27, #3
	eor w0, w0, w27, ror #7
	eor w0, w0, w27, ror #18
	add w26, w26, w0
	lsr w0, w24, #10
	eor w0, w0, w24, ror #17
	eor w0, w0, w24, ror #19
	add w26, w26, w19
	add w26, w26, w0
	ldr w0, [x3, #180]
	add w6, w6, w26
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w28, #3
	eor w0, w0, w28, ror #7
	eor w0, w0, w28, ror #18
	add w27, w27, w0
	lsr w0, w25, #10
	eor w0, w0, w25, ror #17
	eor w0, w0, w25, ror #19
	add w27, w27, w20
	add w27, w27, w0
	ldr w0, [x3, #184]
	add w5, w5, w27
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w12, #3
	eor w0, w0, w12, ror #7
	eor w0, w0, w12, ror #18
	add w28, w28, w0
	lsr w0, w26, #10
	eor w0, w0, w26, ror #17
	eor w0, w0, w26, ror #19
	add w28, w28, w21
	add w28, w28, w0
	ldr w0, [x3, #188]
	add w4, w4, w28
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w13, #3
	eor w0, w0, w13, ror #7
	eor w0, w0, w13, ror #18
	add w12, w12, w0
	lsr w0, w27, #10
	eor w0, w0, w27, ror #17
	eor w0, w0, w27, ror #19
	add w12, w12, w22
	add w12, w12, w0
	ldr w0, [x3, #192]
	add w11, w11, w12
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w14, #3
	eor w0, w0, w14, ror #7
	eor w0, w0, w14, ror #18
	add w13, w13, w0
	lsr w0, w28, #10
	eor w0, w0, w28, ror #17
	eor w0, w0, w28, ror #19
	add w13, w13, w23
	add w13, w13, w0
	ldr w0, [x3, #196]
	add w10, w10, w13
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w15, #3
	eor w0, w0, w15, ror #7
	eor w0, w0, w15, ror #18
	add w14, w14, w0
	lsr w0, w12, #10
	eor w0, w0, w12, ror #17
	eor w0, w0, w12, ror #19
	add w14, w14, w24
	add w14, w14, w0
	ldr w0, [x3, #200]
	add w9, w9, w14
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w16, #3
	eor w0, w0, w16, ror #7
	eor w0, w0, w16, ror #18
	add w15, w15, w0
	lsr w0, w13, #10
	eor w0, w0, w13, ror #17
	eor w0, w0, w13, ror #19
	add w15, w15, w25
	add w15, w15, w0
	ldr w0, [x3, #204]
	add w8, w8, w15
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w17, #3
	eor w0, w0, w17, ror #7
	eor w0, w0, w17, ror #18
	add w16, w16, w0
	lsr w0, w14, #10
	eor w0, w0, w14, ror #17
	eor w0, w0, w14, ror #19
	add w16, w16, w26
	add w16, w16, w0
	ldr w0, [x3, #208]
	add w7, w7, w16
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w19, #3
	eor w0, w0, w19, ror #7
	eor w0, w0, w19, ror #18
	add w17, w17, w0
	lsr w0, w15, #10
	eor w0, w0, w15, ror #17
	eor w0, w0, w15, ror #19
	add w17, w17, w27
	add w17, w17, w0
	ldr w0, [x3, #212]
	add w6, w6, w17
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w20, #3
	eor w0, w0, w20, ror #7
	eor w0, w0, w20, ror #18
	add w19, w19, w0
	lsr w0, w16, #10
	eor w0, w0, w16, ror #17
	eor w0, w0, w16, ror #19
	add w19, w19, w28
	add w19, w19, w0
	ldr w0, [x3, #216]
	add w5, w5, w19
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w21, #3
	eor w0, w0, w21, ror #7
	eor w0, w0, w21, ror #18
	add w20, w20, w0
	lsr w0, w17, #10
	eor w0, w0, w17, ror #17
	eor w0, w0, w17, ror #19
	add w20, w20, w12
	add w20, w20, w0
	ldr w0, [x3, #220]
	add w4, w4, w20
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	lsr w0, w22, #3
	eor w0, w0, w22, ror #7
	eor w0, w0, w22, ror #18
	add w21, w21, w0
	lsr w0, w19, #10
	eor w0, w0, w19, ror #17
	eor w0, w0, w19, ror #19
	add w21, w21, w13
	add w21, w21, w0
	ldr w0, [x3, #224]
	add w11, w11, w21
	add w11, w11, w0
	ror w0, w8, #6
	eor w0, w0, w8, ror #11
	eor w0, w0, w8, ror #25
	add w11, w11, w0
	eor w0, w9, w10
	and w0, w0, w8
	eor w0, w0, w10
	add w11, w11, w0
	add w7, w7, w11
	ror w0, w4, #2
	eor w0, w0, w4, ror #13
	eor w0, w0, w4, ror #22
	add w11, w11, w0
	eor w1, w4, w5
	and w2, w2, w1
	eor w2, w2, w5
	add w11, w11, w2
	lsr w0, w23, #3
	eor w0, w0, w23, ror #7
	eor w0, w0, w23, ror #18
	add w22, w22, w0
	lsr w0, w20, #10
	eor w0, w0, w20, ror #17
	eor w0, w0, w20, ror #19
	add w22, w22, w14
	add w22, w22, w0
	ldr w0, [x3, #228]
	add w10, w10, w22
	add w10, w10, w0
	ror w0, w7, #6
	eor w0, w0, w7, ror #11
	eor w0, w0, w7, ror #25
	add w10, w10, w0
	eor w0, w8, w9
	and w0, w0, w7
	eor w0, w0, w9
	add w10, w10, w0
	add w6, w6, w10
	ror w0, w11, #2
	eor w0, w0, w11, ror #13
	eor w0, w0, w11, ror #22
	add w10, w10, w0
	eor w2, w11, w4
	and w1, w1, w2
	eor w1, w1, w4
	add w10, w10, w1
	lsr w0, w24, #3
	eor w0, w0, w24, ror #7
	eor w0, w0, w24, ror #18
	add w23, w23, w0
	lsr w0, w21, #10
	eor w0, w0, w21, ror #17
	eor w0, w0, w21, ror #19
	add w23, w23, w15
	add w23, w23, w0
	ldr w0, [x3, #232]
	add w9, w9, w23
	add w9, w9, w0
	ror w0, w6, #6
	eor w0, w0, w6, ror #11
	eor w0, w0, w6, ror #25
	add w9, w9, w0
	eor w0, w7, w8
	and w0, w0, w6
	eor w0, w0, w8
	add w9, w9, w0
	add w5, w5, w9
	ror w0, w10, #2
	eor w0, w0, w10, ror #13
	eor w0, w0, w10, ror #22
	add w9, w9, w0
	eor w1, w10, w11
	and w2, w2, w1
	eor w2, w2, w11
	add w9, w9, w2
	lsr w0, w25, #3
	eor w0, w0, w25, ror #7
	eor w0, w0, w25, ror #18
	add w24, w24, w0
	lsr w0, w22, #10
	eor w0, w0, w22, ror #17
	eor w0, w0, w22, ror #19
	add w24, w24, w16
	add w24, w24, w0
	ldr w0, [x3, #236]
	add w8, w8, w24
	add w8, w8, w0
	ror w0, w5, #6
	eor w0, w0, w5, ror #11
	eor w0, w0, w5, ror #25
	add w8, w8, w0
	eor w0, w6, w7
	and w0, w0, w5
	eor w0, w0, w7
	add w8, w8, w0
	add w4, w4, w8
	ror w0, w9, #2
	eor w0, w0, w9, ror #13
	eor w0, w0, w9, ror #22
	add w8, w8, w0
	eor w2, w9, w10
	and w1, w1, w2
	eor w1, w1, w10
	add w8, w8, w1
	lsr w0, w26, #3
	eor w0, w0, w26, ror #7
	eor w0, w0, w26, ror #18
	add w25, w25, w0
	lsr w0, w23, #10
	eor w0, w0, w23, ror #17
	eor w0, w0, w23, ror #19
	add w25, w25, w17
	add w25, w25, w0
	ldr w0, [x3, #240]
	add w7, w7, w25
	add w7, w7, w0
	ror w0, w4, #6
	eor w0, w0, w4, ror #11
	eor w0, w0, w4, ror #25
	add w7, w7, w0
	eor w0, w5, w6
	and w0, w0, w4
	eor w0, w0, w6
	add w7, w7, w0
	add w11, w11, w7
	ror w0, w8, #2
	eor w0, w0, w8, ror #13
	eor w0, w0, w8, ror #22
	add w7, w7, w0
	eor w1, w8, w9
	and w2, w2, w1
	eor w2, w2, w9
	add w7, w7, w2
	lsr w0, w27, #3
	eor w0, w0, w27, ror #7
	eor w0, w0, w27, ror #18
	add w26, w26, w0
	lsr w0, w24, #10
	eor w0, w0, w24, ror #17
	eor w0, w0, w24, ror #19
	add w26, w26, w19
	add w26, w26, w0
	ldr w0, [x3, #244]
	add w6, w6, w26
	add w6, w6, w0
	ror w0, w11, #6
	eor w0, w0, w11, ror #11
	eor w0, w0, w11, ror #25
	add w6, w6, w0
	eor w0, w4, w5
	and w0, w0, w11
	eor w0, w0, w5
	add w6, w6, w0
	add w10, w10, w6
	ror w0, w7, #2
	eor w0, w0, w7, ror #13
	eor w0, w0, w7, ror #22
	add w6, w6, w0
	eor w2, w7, w8
	and w1, w1, w2
	eor w1, w1, w8
	add w6, w6, w1
	lsr w0, w28, #3
	eor w0, w0, w28, ror #7
	eor w0, w0, w28, ror #18
	add w27, w27, w0
	lsr w0, w25, #10
	eor w0, w0, w25, ror #17
	eor w0, w0, w25, ror #19
	add w27, w27, w20
	add w27, w27, w0
	ldr w0, [x3, #248]
	add w5, w5, w27
	add w5, w5, w0
	ror w0, w10, #6
	eor w0, w0, w10, ror #11
	eor w0, w0, w10, ror #25
	add w5, w5, w0
	eor w0, w11, w4
	and w0, w0, w10
	eor w0, w0, w4
	add w5, w5, w0
	add w9, w9, w5
	ror w0, w6, #2
	eor w0, w0, w6, ror #13
	eor w0, w0, w6, ror #22
	add w5, w5, w0
	eor w1, w6, w7
	and w2, w2, w1
	eor w2, w2, w7
	add w5, w5, w2
	lsr w0, w12, #3
	eor w0, w0, w12, ror #7
	eor w0, w0, w12, ror #18
	add w28, w28, w0
	lsr w0, w26, #10
	eor w0, w0, w26, ror #17
	eor w0, w0, w26, ror #19
	add w28, w28, w21
	add w28, w28, w0
	ldr w0, [x3, #252]
	add w4, w4, w28
	add w4, w4, w0
	ror w0, w9, #6
	eor w0, w0, w9, ror #11
	eor w0, w0, w9, ror #25
	add w4, w4, w0
	eor w0, w10, w11
	and w0, w0, w9
	eor w0, w0, w11
	add w4, w4, w0
	add w8, w8, w4
	ror w0, w5, #2
	eor w0, w0, w5, ror #13
	eor w0, w0, w5, ror #22
	add w4, w4, w0
	eor w2, w5, w6
	and w1, w1, w2
	eor w1, w1, w6
	add w4, w4, w1
	umov x0, v16.d[0]
	ldr w12, [x0, #0]
	ldr w13, [x0, #4]
	ldr w14, [x0, #8]
	ldr w15, [x0, #12]
	ldr w16, [x0, #16]
	ldr w17, [x0, #20]
	ldr w19, [x0, #24]
	ldr w20, [x0, #28]
	add w4, w4, w12
	add w5, w5, w13
	add w6, w6, w14
	add w7, w7, w15
	add w8, w8, w16
	add w9, w9, w17
	add w10, w10, w19
	add w11, w11, w20
	str w4, [x0, #0]
	str w5, [x0, #4]
	str w6, [x0, #8]
	str w7, [x0, #12]
	str w8, [x0, #16]
	str w9, [x0, #20]
	str w10, [x0, #24]
	str w11, [x0, #28]
	umov x0, v17.d[0]
	sub x0, x0, #1
	mov v17.d[0], x0
	cbnz x0, 22b
	umov x19, v18.d[0]
	umov x20, v18.d[1]
	umov x21, v19.d[0]
	umov x22, v19.d[1]
	umov x23, v20.d[0]
	umov x24, v20.d[1]
	umov x25, v21.d[0]
	umov x26, v21.d[1]
	umov x27, v22.d[0]
	umov x28, v22.d[1]
	umov x1, v16.d[1]
	b 21f
20:
21:
	ret
	.p2align 6
