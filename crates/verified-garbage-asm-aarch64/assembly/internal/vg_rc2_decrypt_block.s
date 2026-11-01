// The functions of `src/internal/vg_rc2_decrypt_block.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_decrypt_block:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	movz x9, #65535, lsl #0
	ldr x8, [x1, #0]
	add x19, x8, #0
	lsr x19, x19, #0
	lsl x19, x19, #48
	lsr x19, x19, #48
	add x20, x8, #0
	lsr x20, x20, #16
	lsl x20, x20, #48
	lsr x20, x20, #48
	add x21, x8, #0
	lsr x21, x21, #32
	lsl x21, x21, #48
	lsr x21, x21, #48
	add x22, x8, #0
	lsr x22, x22, #48
	lsl x22, x22, #48
	lsr x22, x22, #48
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #126]
	ldrb w5, [x0, #127]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #124]
	ldrb w5, [x0, #125]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #122]
	ldrb w5, [x0, #123]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #120]
	ldrb w5, [x0, #121]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #118]
	ldrb w5, [x0, #119]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #116]
	ldrb w5, [x0, #117]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #114]
	ldrb w5, [x0, #115]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #112]
	ldrb w5, [x0, #113]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #110]
	ldrb w5, [x0, #111]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #108]
	ldrb w5, [x0, #109]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #106]
	ldrb w5, [x0, #107]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #104]
	ldrb w5, [x0, #105]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #102]
	ldrb w5, [x0, #103]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #100]
	ldrb w5, [x0, #101]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #98]
	ldrb w5, [x0, #99]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #96]
	ldrb w5, [x0, #97]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #94]
	ldrb w5, [x0, #95]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #92]
	ldrb w5, [x0, #93]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #90]
	ldrb w5, [x0, #91]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #88]
	ldrb w5, [x0, #89]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x22, x22, x8
	and x22, x22, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x21, x21, x8
	and x21, x21, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x20, x20, x8
	and x20, x20, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x19, x19, x8
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #86]
	ldrb w5, [x0, #87]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #84]
	ldrb w5, [x0, #85]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #82]
	ldrb w5, [x0, #83]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #80]
	ldrb w5, [x0, #81]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #78]
	ldrb w5, [x0, #79]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #76]
	ldrb w5, [x0, #77]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #74]
	ldrb w5, [x0, #75]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #72]
	ldrb w5, [x0, #73]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #70]
	ldrb w5, [x0, #71]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #68]
	ldrb w5, [x0, #69]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #66]
	ldrb w5, [x0, #67]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #64]
	ldrb w5, [x0, #65]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #62]
	ldrb w5, [x0, #63]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #60]
	ldrb w5, [x0, #61]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #58]
	ldrb w5, [x0, #59]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #56]
	ldrb w5, [x0, #57]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #54]
	ldrb w5, [x0, #55]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #52]
	ldrb w5, [x0, #53]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #50]
	ldrb w5, [x0, #51]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #48]
	ldrb w5, [x0, #49]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #46]
	ldrb w5, [x0, #47]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #44]
	ldrb w5, [x0, #45]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #42]
	ldrb w5, [x0, #43]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #40]
	ldrb w5, [x0, #41]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x22, x22, x8
	and x22, x22, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x21, x21, x8
	and x21, x21, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x20, x20, x8
	and x20, x20, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x19, x19, x8
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #38]
	ldrb w5, [x0, #39]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #36]
	ldrb w5, [x0, #37]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #34]
	ldrb w5, [x0, #35]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #32]
	ldrb w5, [x0, #33]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #30]
	ldrb w5, [x0, #31]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #28]
	ldrb w5, [x0, #29]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #26]
	ldrb w5, [x0, #27]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #24]
	ldrb w5, [x0, #25]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #22]
	ldrb w5, [x0, #23]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #20]
	ldrb w5, [x0, #21]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #18]
	ldrb w5, [x0, #19]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #16]
	ldrb w5, [x0, #17]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #14]
	ldrb w5, [x0, #15]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #12]
	ldrb w5, [x0, #13]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #10]
	ldrb w5, [x0, #11]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #8]
	ldrb w5, [x0, #9]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #6]
	ldrb w5, [x0, #7]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #4]
	ldrb w5, [x0, #5]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #2]
	ldrb w5, [x0, #3]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #0]
	ldrb w5, [x0, #1]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x19, #0
	ror x3, x20, #48
	orr x8, x8, x3
	ror x3, x21, #32
	orr x8, x8, x3
	ror x3, x22, #16
	orr x8, x8, x3
	str x8, [x1, #0]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ret
	.p2align 6
