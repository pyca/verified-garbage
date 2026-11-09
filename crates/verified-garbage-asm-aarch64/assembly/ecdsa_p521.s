// The functions of `src/ecdsa_p521.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_verify:
	sub sp, sp, #80
	add x5, sp, #0
	lsr x10, x2, #7
	movz x11, #127, lsl #0
	and x12, x2, x11
	add x12, x12, #62
	lsr x12, x12, #7
	orr x11, x10, x12
	cbnz x11, 20f
	movz x12, #0, lsl #0
	strb w12, [x5, #0]
	strb w12, [x5, #1]
	strb w12, [x5, #2]
	strb w12, [x5, #3]
	strb w12, [x5, #4]
	strb w12, [x5, #5]
	strb w12, [x5, #6]
	strb w12, [x5, #7]
	strb w12, [x5, #8]
	strb w12, [x5, #9]
	strb w12, [x5, #10]
	strb w12, [x5, #11]
	strb w12, [x5, #12]
	strb w12, [x5, #13]
	strb w12, [x5, #14]
	strb w12, [x5, #15]
	strb w12, [x5, #16]
	strb w12, [x5, #17]
	strb w12, [x5, #18]
	strb w12, [x5, #19]
	strb w12, [x5, #20]
	strb w12, [x5, #21]
	strb w12, [x5, #22]
	strb w12, [x5, #23]
	strb w12, [x5, #24]
	strb w12, [x5, #25]
	strb w12, [x5, #26]
	strb w12, [x5, #27]
	strb w12, [x5, #28]
	strb w12, [x5, #29]
	strb w12, [x5, #30]
	strb w12, [x5, #31]
	strb w12, [x5, #32]
	strb w12, [x5, #33]
	strb w12, [x5, #34]
	strb w12, [x5, #35]
	strb w12, [x5, #36]
	strb w12, [x5, #37]
	strb w12, [x5, #38]
	strb w12, [x5, #39]
	strb w12, [x5, #40]
	strb w12, [x5, #41]
	strb w12, [x5, #42]
	strb w12, [x5, #43]
	strb w12, [x5, #44]
	strb w12, [x5, #45]
	strb w12, [x5, #46]
	strb w12, [x5, #47]
	strb w12, [x5, #48]
	strb w12, [x5, #49]
	strb w12, [x5, #50]
	strb w12, [x5, #51]
	strb w12, [x5, #52]
	strb w12, [x5, #53]
	strb w12, [x5, #54]
	strb w12, [x5, #55]
	strb w12, [x5, #56]
	strb w12, [x5, #57]
	strb w12, [x5, #58]
	strb w12, [x5, #59]
	strb w12, [x5, #60]
	strb w12, [x5, #61]
	strb w12, [x5, #62]
	strb w12, [x5, #63]
	strb w12, [x5, #64]
	strb w12, [x5, #65]
	strb w12, [x5, #66]
	strb w12, [x5, #67]
	strb w12, [x5, #68]
	strb w12, [x5, #69]
	strb w12, [x5, #70]
	strb w12, [x5, #71]
	add x13, x5, #66
	sub x13, x13, x2
	cbz x2, 22f
24:
	ldrb w9, [x1, #0]
	strb w9, [x13, #0]
	add x1, x1, #1
	add x13, x13, #1
	sub x2, x2, #1
	cbnz x2, 24b
	b 23f
22:
23:
	ldrb w9, [x5, #0]
	ldrb w10, [x5, #1]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #0]
	ldrb w9, [x5, #1]
	ldrb w10, [x5, #2]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #1]
	ldrb w9, [x5, #2]
	ldrb w10, [x5, #3]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #2]
	ldrb w9, [x5, #3]
	ldrb w10, [x5, #4]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #3]
	ldrb w9, [x5, #4]
	ldrb w10, [x5, #5]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #4]
	ldrb w9, [x5, #5]
	ldrb w10, [x5, #6]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #5]
	ldrb w9, [x5, #6]
	ldrb w10, [x5, #7]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #6]
	ldrb w9, [x5, #7]
	ldrb w10, [x5, #8]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #7]
	ldrb w9, [x5, #8]
	ldrb w10, [x5, #9]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #8]
	ldrb w9, [x5, #9]
	ldrb w10, [x5, #10]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #9]
	ldrb w9, [x5, #10]
	ldrb w10, [x5, #11]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #10]
	ldrb w9, [x5, #11]
	ldrb w10, [x5, #12]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #11]
	ldrb w9, [x5, #12]
	ldrb w10, [x5, #13]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #12]
	ldrb w9, [x5, #13]
	ldrb w10, [x5, #14]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #13]
	ldrb w9, [x5, #14]
	ldrb w10, [x5, #15]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #14]
	ldrb w9, [x5, #15]
	ldrb w10, [x5, #16]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #15]
	ldrb w9, [x5, #16]
	ldrb w10, [x5, #17]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #16]
	ldrb w9, [x5, #17]
	ldrb w10, [x5, #18]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #17]
	ldrb w9, [x5, #18]
	ldrb w10, [x5, #19]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #18]
	ldrb w9, [x5, #19]
	ldrb w10, [x5, #20]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #19]
	ldrb w9, [x5, #20]
	ldrb w10, [x5, #21]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #20]
	ldrb w9, [x5, #21]
	ldrb w10, [x5, #22]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #21]
	ldrb w9, [x5, #22]
	ldrb w10, [x5, #23]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #22]
	ldrb w9, [x5, #23]
	ldrb w10, [x5, #24]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #23]
	ldrb w9, [x5, #24]
	ldrb w10, [x5, #25]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #24]
	ldrb w9, [x5, #25]
	ldrb w10, [x5, #26]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #25]
	ldrb w9, [x5, #26]
	ldrb w10, [x5, #27]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #26]
	ldrb w9, [x5, #27]
	ldrb w10, [x5, #28]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #27]
	ldrb w9, [x5, #28]
	ldrb w10, [x5, #29]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #28]
	ldrb w9, [x5, #29]
	ldrb w10, [x5, #30]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #29]
	ldrb w9, [x5, #30]
	ldrb w10, [x5, #31]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #30]
	ldrb w9, [x5, #31]
	ldrb w10, [x5, #32]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #31]
	ldrb w9, [x5, #32]
	ldrb w10, [x5, #33]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #32]
	ldrb w9, [x5, #33]
	ldrb w10, [x5, #34]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #33]
	ldrb w9, [x5, #34]
	ldrb w10, [x5, #35]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #34]
	ldrb w9, [x5, #35]
	ldrb w10, [x5, #36]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #35]
	ldrb w9, [x5, #36]
	ldrb w10, [x5, #37]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #36]
	ldrb w9, [x5, #37]
	ldrb w10, [x5, #38]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #37]
	ldrb w9, [x5, #38]
	ldrb w10, [x5, #39]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #38]
	ldrb w9, [x5, #39]
	ldrb w10, [x5, #40]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #39]
	ldrb w9, [x5, #40]
	ldrb w10, [x5, #41]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #40]
	ldrb w9, [x5, #41]
	ldrb w10, [x5, #42]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #41]
	ldrb w9, [x5, #42]
	ldrb w10, [x5, #43]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #42]
	ldrb w9, [x5, #43]
	ldrb w10, [x5, #44]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #43]
	ldrb w9, [x5, #44]
	ldrb w10, [x5, #45]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #44]
	ldrb w9, [x5, #45]
	ldrb w10, [x5, #46]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #45]
	ldrb w9, [x5, #46]
	ldrb w10, [x5, #47]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #46]
	ldrb w9, [x5, #47]
	ldrb w10, [x5, #48]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #47]
	ldrb w9, [x5, #48]
	ldrb w10, [x5, #49]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #48]
	ldrb w9, [x5, #49]
	ldrb w10, [x5, #50]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #49]
	ldrb w9, [x5, #50]
	ldrb w10, [x5, #51]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #50]
	ldrb w9, [x5, #51]
	ldrb w10, [x5, #52]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #51]
	ldrb w9, [x5, #52]
	ldrb w10, [x5, #53]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #52]
	ldrb w9, [x5, #53]
	ldrb w10, [x5, #54]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #53]
	ldrb w9, [x5, #54]
	ldrb w10, [x5, #55]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #54]
	ldrb w9, [x5, #55]
	ldrb w10, [x5, #56]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #55]
	ldrb w9, [x5, #56]
	ldrb w10, [x5, #57]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #56]
	ldrb w9, [x5, #57]
	ldrb w10, [x5, #58]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #57]
	ldrb w9, [x5, #58]
	ldrb w10, [x5, #59]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #58]
	ldrb w9, [x5, #59]
	ldrb w10, [x5, #60]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #59]
	ldrb w9, [x5, #60]
	ldrb w10, [x5, #61]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #60]
	ldrb w9, [x5, #61]
	ldrb w10, [x5, #62]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #61]
	ldrb w9, [x5, #62]
	ldrb w10, [x5, #63]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #62]
	ldrb w9, [x5, #63]
	ldrb w10, [x5, #64]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #63]
	ldrb w9, [x5, #64]
	ldrb w10, [x5, #65]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #64]
	ldrb w9, [x5, #65]
	ldrb w10, [x5, #66]
	lsl x9, x9, #7
	lsr x10, x10, #1
	add x9, x9, x10
	strb w9, [x5, #65]
	b 21f
20:
	ldrb w9, [x1, #0]
	strb w9, [x5, #0]
	ldrb w9, [x1, #1]
	strb w9, [x5, #1]
	ldrb w9, [x1, #2]
	strb w9, [x5, #2]
	ldrb w9, [x1, #3]
	strb w9, [x5, #3]
	ldrb w9, [x1, #4]
	strb w9, [x5, #4]
	ldrb w9, [x1, #5]
	strb w9, [x5, #5]
	ldrb w9, [x1, #6]
	strb w9, [x5, #6]
	ldrb w9, [x1, #7]
	strb w9, [x5, #7]
	ldrb w9, [x1, #8]
	strb w9, [x5, #8]
	ldrb w9, [x1, #9]
	strb w9, [x5, #9]
	ldrb w9, [x1, #10]
	strb w9, [x5, #10]
	ldrb w9, [x1, #11]
	strb w9, [x5, #11]
	ldrb w9, [x1, #12]
	strb w9, [x5, #12]
	ldrb w9, [x1, #13]
	strb w9, [x5, #13]
	ldrb w9, [x1, #14]
	strb w9, [x5, #14]
	ldrb w9, [x1, #15]
	strb w9, [x5, #15]
	ldrb w9, [x1, #16]
	strb w9, [x5, #16]
	ldrb w9, [x1, #17]
	strb w9, [x5, #17]
	ldrb w9, [x1, #18]
	strb w9, [x5, #18]
	ldrb w9, [x1, #19]
	strb w9, [x5, #19]
	ldrb w9, [x1, #20]
	strb w9, [x5, #20]
	ldrb w9, [x1, #21]
	strb w9, [x5, #21]
	ldrb w9, [x1, #22]
	strb w9, [x5, #22]
	ldrb w9, [x1, #23]
	strb w9, [x5, #23]
	ldrb w9, [x1, #24]
	strb w9, [x5, #24]
	ldrb w9, [x1, #25]
	strb w9, [x5, #25]
	ldrb w9, [x1, #26]
	strb w9, [x5, #26]
	ldrb w9, [x1, #27]
	strb w9, [x5, #27]
	ldrb w9, [x1, #28]
	strb w9, [x5, #28]
	ldrb w9, [x1, #29]
	strb w9, [x5, #29]
	ldrb w9, [x1, #30]
	strb w9, [x5, #30]
	ldrb w9, [x1, #31]
	strb w9, [x5, #31]
	ldrb w9, [x1, #32]
	strb w9, [x5, #32]
	ldrb w9, [x1, #33]
	strb w9, [x5, #33]
	ldrb w9, [x1, #34]
	strb w9, [x5, #34]
	ldrb w9, [x1, #35]
	strb w9, [x5, #35]
	ldrb w9, [x1, #36]
	strb w9, [x5, #36]
	ldrb w9, [x1, #37]
	strb w9, [x5, #37]
	ldrb w9, [x1, #38]
	strb w9, [x5, #38]
	ldrb w9, [x1, #39]
	strb w9, [x5, #39]
	ldrb w9, [x1, #40]
	strb w9, [x5, #40]
	ldrb w9, [x1, #41]
	strb w9, [x5, #41]
	ldrb w9, [x1, #42]
	strb w9, [x5, #42]
	ldrb w9, [x1, #43]
	strb w9, [x5, #43]
	ldrb w9, [x1, #44]
	strb w9, [x5, #44]
	ldrb w9, [x1, #45]
	strb w9, [x5, #45]
	ldrb w9, [x1, #46]
	strb w9, [x5, #46]
	ldrb w9, [x1, #47]
	strb w9, [x5, #47]
	ldrb w9, [x1, #48]
	strb w9, [x5, #48]
	ldrb w9, [x1, #49]
	strb w9, [x5, #49]
	ldrb w9, [x1, #50]
	strb w9, [x5, #50]
	ldrb w9, [x1, #51]
	strb w9, [x5, #51]
	ldrb w9, [x1, #52]
	strb w9, [x5, #52]
	ldrb w9, [x1, #53]
	strb w9, [x5, #53]
	ldrb w9, [x1, #54]
	strb w9, [x5, #54]
	ldrb w9, [x1, #55]
	strb w9, [x5, #55]
	ldrb w9, [x1, #56]
	strb w9, [x5, #56]
	ldrb w9, [x1, #57]
	strb w9, [x5, #57]
	ldrb w9, [x1, #58]
	strb w9, [x5, #58]
	ldrb w9, [x1, #59]
	strb w9, [x5, #59]
	ldrb w9, [x1, #60]
	strb w9, [x5, #60]
	ldrb w9, [x1, #61]
	strb w9, [x5, #61]
	ldrb w9, [x1, #62]
	strb w9, [x5, #62]
	ldrb w9, [x1, #63]
	strb w9, [x5, #63]
	ldrb w9, [x1, #64]
	strb w9, [x5, #64]
	ldrb w9, [x1, #65]
	strb w9, [x5, #65]
21:
	add x1, x5, #0
	add x2, x3, #0
	add x3, x4, #0
	add x4, x3, #0
	add x6, x0, #0
	add x3, x2, #0
	add x8, x2, #66
	add x2, x0, #1
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	str x25, [x4, #48]
	str x30, [x4, #56]
	add x20, x0, #0
	add x0, x4, #0
	add x17, x3, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2296]
	add x17, x3, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2304]
	add x17, x3, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2312]
	add x17, x3, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2320]
	add x17, x3, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2328]
	add x17, x3, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2336]
	add x17, x3, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2344]
	add x17, x3, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2352]
	ldr x5, [x3, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2360]
	add x17, x1, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2368]
	add x17, x1, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2376]
	add x17, x1, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2384]
	add x17, x1, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2392]
	add x17, x1, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2400]
	add x17, x1, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2408]
	add x17, x1, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2416]
	add x17, x1, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2424]
	ldr x5, [x1, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2432]
	add x17, x2, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2440]
	add x17, x2, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2448]
	add x17, x2, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2456]
	add x17, x2, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2464]
	add x17, x2, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2472]
	add x17, x2, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2480]
	add x17, x2, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2488]
	add x17, x2, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2496]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2504]
	ldr x1, [x0, #2368]
	ldr x2, [x0, #2376]
	extr x1, x2, x1, #7
	str x1, [x0, #2368]
	ldr x1, [x0, #2376]
	ldr x2, [x0, #2384]
	extr x1, x2, x1, #7
	str x1, [x0, #2376]
	ldr x1, [x0, #2384]
	ldr x2, [x0, #2392]
	extr x1, x2, x1, #7
	str x1, [x0, #2384]
	ldr x1, [x0, #2392]
	ldr x2, [x0, #2400]
	extr x1, x2, x1, #7
	str x1, [x0, #2392]
	ldr x1, [x0, #2400]
	ldr x2, [x0, #2408]
	extr x1, x2, x1, #7
	str x1, [x0, #2400]
	ldr x1, [x0, #2408]
	ldr x2, [x0, #2416]
	extr x1, x2, x1, #7
	str x1, [x0, #2408]
	ldr x1, [x0, #2416]
	ldr x2, [x0, #2424]
	extr x1, x2, x1, #7
	str x1, [x0, #2416]
	ldr x1, [x0, #2424]
	ldr x2, [x0, #2432]
	extr x1, x2, x1, #7
	str x1, [x0, #2424]
	ldr x1, [x0, #2432]
	lsr x1, x1, #7
	str x1, [x0, #2432]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #88]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #96]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #120]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #128]
	movz x1, #25609, lsl #0
	movk x1, #37176, lsl #16
	movk x1, #46878, lsl #32
	movk x1, #47983, lsl #48
	str x1, [x0, #136]
	movz x1, #18350, lsl #0
	movk x1, #35228, lsl #16
	movk x1, #51640, lsl #32
	movk x1, #15285, lsl #48
	str x1, [x0, #144]
	movz x1, #42448, lsl #0
	movk x1, #63241, lsl #16
	movk x1, #328, lsl #32
	movk x1, #32716, lsl #48
	str x1, [x0, #152]
	movz x1, #38507, lsl #0
	movk x1, #48943, lsl #16
	movk x1, #34691, lsl #32
	movk x1, #20870, lsl #48
	str x1, [x0, #160]
	movz x1, #65530, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #168]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #176]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #184]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #192]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #488]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65151, lsl #48
	str x1, [x0, #496]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #504]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #512]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #520]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #528]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #536]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #544]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #560]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #568]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #576]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #584]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #592]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #600]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #608]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #616]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #624]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #632]
	movz x1, #49409, lsl #0
	movk x1, #33197, lsl #16
	movk x1, #41315, lsl #32
	movk x1, #45873, lsl #48
	str x1, [x0, #640]
	movz x1, #29406, lsl #0
	movk x1, #6369, lsl #16
	movk x1, #48959, lsl #32
	movk x1, #19964, lsl #48
	str x1, [x0, #648]
	movz x1, #46369, lsl #0
	movk x1, #57538, lsl #16
	movk x1, #42073, lsl #32
	movk x1, #28441, lsl #48
	str x1, [x0, #656]
	movz x1, #32724, lsl #0
	movk x1, #37841, lsl #16
	movk x1, #3808, lsl #32
	movk x1, #38015, lsl #48
	str x1, [x0, #664]
	movz x1, #62380, lsl #0
	movk x1, #15351, lsl #16
	movk x1, #42415, lsl #32
	movk x1, #56656, lsl #48
	str x1, [x0, #672]
	movz x1, #42654, lsl #0
	movk x1, #45109, lsl #16
	movk x1, #5207, lsl #32
	movk x1, #37116, lsl #48
	str x1, [x0, #680]
	movz x1, #40922, lsl #0
	movk x1, #40066, lsl #16
	movk x1, #12864, lsl #32
	movk x1, #8526, lsl #48
	str x1, [x0, #688]
	movz x1, #51930, lsl #0
	movk x1, #45841, lsl #16
	movk x1, #8037, lsl #32
	movk x1, #59087, lsl #48
	str x1, [x0, #696]
	movz x1, #116, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #704]
	movz x1, #9870, lsl #0
	movk x1, #23198, lsl #16
	movk x1, #3658, lsl #32
	movk x1, #10310, lsl #48
	str x1, [x0, #712]
	movz x1, #59571, lsl #0
	movk x1, #15183, lsl #16
	movk x1, #24394, lsl #32
	movk x1, #8260, lsl #48
	str x1, [x0, #720]
	movz x1, #14689, lsl #0
	movk x1, #17233, lsl #16
	movk x1, #40504, lsl #32
	movk x1, #45210, lsl #48
	str x1, [x0, #728]
	movz x1, #54915, lsl #0
	movk x1, #32927, lsl #16
	movk x1, #43100, lsl #32
	movk x1, #8290, lsl #48
	str x1, [x0, #736]
	movz x1, #31251, lsl #0
	movk x1, #19631, lsl #16
	movk x1, #63289, lsl #32
	movk x1, #5707, lsl #48
	str x1, [x0, #744]
	movz x1, #40755, lsl #0
	movk x1, #35731, lsl #16
	movk x1, #55262, lsl #32
	movk x1, #13323, lsl #48
	str x1, [x0, #752]
	movz x1, #52642, lsl #0
	movk x1, #9387, lsl #16
	movk x1, #31394, lsl #32
	movk x1, #60620, lsl #48
	str x1, [x0, #760]
	movz x1, #16013, lsl #0
	movk x1, #55830, lsl #16
	movk x1, #17711, lsl #32
	movk x1, #558, lsl #48
	str x1, [x0, #768]
	movz x1, #480, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #776]
	movz x1, #56580, lsl #0
	movk x1, #53013, lsl #16
	movk x1, #53325, lsl #32
	movk x1, #4988, lsl #48
	str x1, [x0, #784]
	movz x1, #32419, lsl #0
	movk x1, #58708, lsl #16
	movk x1, #47836, lsl #32
	movk x1, #63239, lsl #48
	str x1, [x0, #792]
	movz x1, #29695, lsl #0
	movk x1, #31045, lsl #16
	movk x1, #36152, lsl #32
	movk x1, #4775, lsl #48
	str x1, [x0, #800]
	movz x1, #24070, lsl #0
	movk x1, #22519, lsl #16
	movk x1, #7925, lsl #32
	movk x1, #54130, lsl #48
	str x1, [x0, #808]
	movz x1, #51163, lsl #0
	movk x1, #11849, lsl #16
	movk x1, #9176, lsl #32
	movk x1, #56686, lsl #48
	str x1, [x0, #816]
	movz x1, #28222, lsl #0
	movk x1, #46965, lsl #16
	movk x1, #53570, lsl #32
	movk x1, #53235, lsl #48
	str x1, [x0, #824]
	movz x1, #26556, lsl #0
	movk x1, #43237, lsl #16
	movk x1, #28001, lsl #32
	movk x1, #23500, lsl #48
	str x1, [x0, #832]
	movz x1, #3397, lsl #0
	movk x1, #18733, lsl #16
	movk x1, #977, lsl #32
	movk x1, #11662, lsl #48
	str x1, [x0, #840]
	movz x1, #61, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #848]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #64384, lsl #48
	str x1, [x0, #856]
	movz x1, #25549, lsl #0
	movk x1, #28855, lsl #16
	movk x1, #18468, lsl #32
	movk x1, #10402, lsl #48
	str x1, [x0, #864]
	movz x1, #12764, lsl #0
	movk x1, #9147, lsl #16
	movk x1, #9499, lsl #32
	movk x1, #6114, lsl #48
	str x1, [x0, #872]
	movz x1, #31533, lsl #0
	movk x1, #23428, lsl #16
	movk x1, #6655, lsl #32
	movk x1, #51776, lsl #48
	str x1, [x0, #880]
	movz x1, #26676, lsl #0
	movk x1, #15904, lsl #16
	movk x1, #15548, lsl #32
	movk x1, #727, lsl #48
	str x1, [x0, #888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1080]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1088]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1096]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1104]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1120]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1128]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #3232]
	movz x19, #72, lsl #0
	movz x5, #1, lsl #0
25:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #2296]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #3304]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #3305]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #3306]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #3307]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #3308]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #3309]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #3310]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #3311]
	cbnz x19, 25b
	add x17, x8, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2224]
	add x17, x8, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2232]
	add x17, x8, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2240]
	add x17, x8, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2248]
	add x17, x8, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2256]
	add x17, x8, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2264]
	add x17, x8, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2272]
	add x17, x8, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2280]
	ldr x5, [x8, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2872]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #16384, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2928]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2936]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #2944]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #2952]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #2960]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #2968]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #2976]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #2984]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #2992]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #3000]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #3008]
	add x2, x6, #67
	add x17, x2, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2656]
	add x17, x2, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2664]
	add x17, x2, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2672]
	add x17, x2, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2680]
	add x17, x2, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2688]
	add x17, x2, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2696]
	add x17, x2, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2704]
	add x17, x2, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2712]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2720]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	mov v28.d[0], x30
	bl {vg_p521_check_point}
	umov x30, v28.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2296]
	ldr x2, [x0, #136]
	subs x16, x1, x2
	ldr x1, [x0, #2304]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2312]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2320]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2328]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2336]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2344]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	ldr x1, [x0, #2352]
	ldr x2, [x0, #192]
	sbcs x16, x1, x2
	ldr x1, [x0, #2360]
	ldr x2, [x0, #200]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2296]
	ldr x2, [x0, #2304]
	orr x1, x1, x2
	ldr x2, [x0, #2312]
	orr x1, x1, x2
	ldr x2, [x0, #2320]
	orr x1, x1, x2
	ldr x2, [x0, #2328]
	orr x1, x1, x2
	ldr x2, [x0, #2336]
	orr x1, x1, x2
	ldr x2, [x0, #2344]
	orr x1, x1, x2
	ldr x2, [x0, #2352]
	orr x1, x1, x2
	ldr x2, [x0, #2360]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2224]
	ldr x2, [x0, #136]
	subs x16, x1, x2
	ldr x1, [x0, #2232]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2240]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2248]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2256]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2264]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2272]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	ldr x1, [x0, #2280]
	ldr x2, [x0, #192]
	sbcs x16, x1, x2
	ldr x1, [x0, #2288]
	ldr x2, [x0, #200]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2224]
	ldr x2, [x0, #2232]
	orr x1, x1, x2
	ldr x2, [x0, #2240]
	orr x1, x1, x2
	ldr x2, [x0, #2248]
	orr x1, x1, x2
	ldr x2, [x0, #2256]
	orr x1, x1, x2
	ldr x2, [x0, #2264]
	orr x1, x1, x2
	ldr x2, [x0, #2272]
	orr x1, x1, x2
	ldr x2, [x0, #2280]
	orr x1, x1, x2
	ldr x2, [x0, #2288]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	mov v29.d[0], x30
	movz x1, #2728, lsl #0
	movz x2, #2224, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	bl {vg_p521_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2944, lsl #0
	movz x2, #2368, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2872, lsl #0
	movz x2, #2296, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3016, lsl #0
	movz x2, #2944, lsl #0
	movz x3, #2152, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3088, lsl #0
	movz x2, #2872, lsl #0
	movz x3, #2152, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2512, lsl #0
	movz x2, #3016, lsl #0
	movz x3, #352, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2584, lsl #0
	movz x2, #3088, lsl #0
	movz x3, #352, lsl #0
	bl {vg_p521_mul_mod_n}
	umov x30, v29.d[0]
	ldr x5, [x0, #2512]
	ldr x6, [x0, #2520]
	ldr x7, [x0, #2528]
	ldr x8, [x0, #2536]
	ldr x9, [x0, #2544]
	ldr x10, [x0, #2552]
	ldr x11, [x0, #2560]
	ldr x12, [x0, #2568]
	ldr x13, [x0, #2576]
	movz x14, #0, lsl #0
	movz x15, #127, lsl #0
	movz x21, #64, lsl #0
	movz x22, #0, lsl #0
	movz x23, #1, lsl #0
	movz x19, #577, lsl #0
	add x20, x0, #3304
26:
	and x1, x5, x23
	cbnz x1, 27f
	movz x2, #0, lsl #0
	b 28f
27:
	and x2, x5, x15
	and x3, x2, x21
	lsl x3, x3, #1
	sub x2, x2, x3
28:
	strb w2, [x20, #0]
	add x20, x20, #1
	lsr x3, x2, #63
	sub x3, x22, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbcs x9, x9, x3
	sbcs x10, x10, x3
	sbcs x11, x11, x3
	sbcs x12, x12, x3
	sbcs x13, x13, x3
	sbcs x14, x14, x3
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	extr x9, x10, x9, #1
	extr x10, x11, x10, #1
	extr x11, x12, x11, #1
	extr x12, x13, x12, #1
	extr x13, x14, x13, #1
	lsr x14, x14, #1
	sub x19, x19, #1
	cbnz x19, 26b
	ldr x5, [x0, #2584]
	ldr x6, [x0, #2592]
	ldr x7, [x0, #2600]
	ldr x8, [x0, #2608]
	ldr x9, [x0, #2616]
	ldr x10, [x0, #2624]
	ldr x11, [x0, #2632]
	ldr x12, [x0, #2640]
	ldr x13, [x0, #2648]
	movz x14, #0, lsl #0
	movz x15, #31, lsl #0
	movz x21, #16, lsl #0
	movz x22, #0, lsl #0
	movz x23, #1, lsl #0
	movz x19, #577, lsl #0
	add x20, x0, #4024
29:
	and x1, x5, x23
	cbnz x1, 210f
	movz x2, #0, lsl #0
	b 211f
210:
	and x2, x5, x15
	and x3, x2, x21
	lsl x3, x3, #1
	sub x2, x2, x3
211:
	strb w2, [x20, #0]
	add x20, x20, #1
	lsr x3, x2, #63
	sub x3, x22, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbcs x9, x9, x3
	sbcs x10, x10, x3
	sbcs x11, x11, x3
	sbcs x12, x12, x3
	sbcs x13, x13, x3
	sbcs x14, x14, x3
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	extr x9, x10, x9, #1
	extr x10, x11, x10, #1
	extr x11, x12, x11, #1
	extr x12, x13, x12, #1
	extr x13, x14, x13, #1
	lsr x14, x14, #1
	sub x19, x19, #1
	cbnz x19, 29b
	ldr x1, [x0, #2800]
	str x1, [x0, #1072]
	ldr x1, [x0, #2808]
	str x1, [x0, #1080]
	ldr x1, [x0, #2816]
	str x1, [x0, #1088]
	ldr x1, [x0, #2824]
	str x1, [x0, #1096]
	ldr x1, [x0, #2832]
	str x1, [x0, #1104]
	ldr x1, [x0, #2840]
	str x1, [x0, #1112]
	ldr x1, [x0, #2848]
	str x1, [x0, #1120]
	ldr x1, [x0, #2856]
	str x1, [x0, #1128]
	ldr x1, [x0, #2864]
	str x1, [x0, #1136]
	ldr x1, [x0, #3160]
	str x1, [x0, #1144]
	ldr x1, [x0, #3168]
	str x1, [x0, #1152]
	ldr x1, [x0, #3176]
	str x1, [x0, #1160]
	ldr x1, [x0, #3184]
	str x1, [x0, #1168]
	ldr x1, [x0, #3192]
	str x1, [x0, #1176]
	ldr x1, [x0, #3200]
	str x1, [x0, #1184]
	ldr x1, [x0, #3208]
	str x1, [x0, #1192]
	ldr x1, [x0, #3216]
	str x1, [x0, #1200]
	ldr x1, [x0, #3224]
	str x1, [x0, #1208]
	ldr x1, [x0, #424]
	str x1, [x0, #1216]
	ldr x1, [x0, #432]
	str x1, [x0, #1224]
	ldr x1, [x0, #440]
	str x1, [x0, #1232]
	ldr x1, [x0, #448]
	str x1, [x0, #1240]
	ldr x1, [x0, #456]
	str x1, [x0, #1248]
	ldr x1, [x0, #464]
	str x1, [x0, #1256]
	ldr x1, [x0, #472]
	str x1, [x0, #1264]
	ldr x1, [x0, #480]
	str x1, [x0, #1272]
	ldr x1, [x0, #488]
	str x1, [x0, #1280]
	add x20, x0, #0
	ldr x4, [x0, #1072]
	str x4, [x20, #5176]
	ldr x4, [x0, #1080]
	str x4, [x20, #5184]
	ldr x4, [x0, #1088]
	str x4, [x20, #5192]
	ldr x4, [x0, #1096]
	str x4, [x20, #5200]
	ldr x4, [x0, #1104]
	str x4, [x20, #5208]
	ldr x4, [x0, #1112]
	str x4, [x20, #5216]
	ldr x4, [x0, #1120]
	str x4, [x20, #5224]
	ldr x4, [x0, #1128]
	str x4, [x20, #5232]
	ldr x4, [x0, #1136]
	str x4, [x20, #5240]
	ldr x4, [x0, #1144]
	str x4, [x20, #5248]
	ldr x4, [x0, #1152]
	str x4, [x20, #5256]
	ldr x4, [x0, #1160]
	str x4, [x20, #5264]
	ldr x4, [x0, #1168]
	str x4, [x20, #5272]
	ldr x4, [x0, #1176]
	str x4, [x20, #5280]
	ldr x4, [x0, #1184]
	str x4, [x20, #5288]
	ldr x4, [x0, #1192]
	str x4, [x20, #5296]
	ldr x4, [x0, #1200]
	str x4, [x20, #5304]
	ldr x4, [x0, #1208]
	str x4, [x20, #5312]
	ldr x4, [x0, #1216]
	str x4, [x20, #5320]
	ldr x4, [x0, #1224]
	str x4, [x20, #5328]
	ldr x4, [x0, #1232]
	str x4, [x20, #5336]
	ldr x4, [x0, #1240]
	str x4, [x20, #5344]
	ldr x4, [x0, #1248]
	str x4, [x20, #5352]
	ldr x4, [x0, #1256]
	str x4, [x20, #5360]
	ldr x4, [x0, #1264]
	str x4, [x20, #5368]
	ldr x4, [x0, #1272]
	str x4, [x20, #5376]
	ldr x4, [x0, #1280]
	str x4, [x20, #5384]
	add x20, x20, #216
	movz x19, #7, lsl #0
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #2800, lsl #0
	movz x3, #2800, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #3160, lsl #0
	movz x3, #3160, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #2800, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1072]
	adds x8, x8, x2
	ldr x2, [x0, #1080]
	adcs x9, x9, x2
	ldr x2, [x0, #1088]
	adcs x10, x10, x2
	ldr x2, [x0, #1096]
	adcs x11, x11, x2
	ldr x2, [x0, #1104]
	adcs x12, x12, x2
	ldr x2, [x0, #1112]
	adcs x13, x13, x2
	ldr x2, [x0, #1120]
	adcs x14, x14, x2
	ldr x2, [x0, #1128]
	adcs x15, x15, x2
	ldr x2, [x0, #1136]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1072]
	adds x8, x8, x2
	ldr x2, [x0, #1080]
	adcs x9, x9, x2
	ldr x2, [x0, #1088]
	adcs x10, x10, x2
	ldr x2, [x0, #1096]
	adcs x11, x11, x2
	ldr x2, [x0, #1104]
	adcs x12, x12, x2
	ldr x2, [x0, #1112]
	adcs x13, x13, x2
	ldr x2, [x0, #1120]
	adcs x14, x14, x2
	ldr x2, [x0, #1128]
	adcs x15, x15, x2
	ldr x2, [x0, #1136]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1720]
	ldr x9, [x0, #1728]
	ldr x10, [x0, #1736]
	ldr x11, [x0, #1744]
	ldr x12, [x0, #1752]
	ldr x13, [x0, #1760]
	ldr x14, [x0, #1768]
	ldr x15, [x0, #1776]
	ldr x21, [x0, #1784]
	ldr x2, [x0, #424]
	subs x8, x8, x2
	ldr x2, [x0, #432]
	sbcs x9, x9, x2
	ldr x2, [x0, #440]
	sbcs x10, x10, x2
	ldr x2, [x0, #448]
	sbcs x11, x11, x2
	ldr x2, [x0, #456]
	sbcs x12, x12, x2
	ldr x2, [x0, #464]
	sbcs x13, x13, x2
	ldr x2, [x0, #472]
	sbcs x14, x14, x2
	ldr x2, [x0, #480]
	sbcs x15, x15, x2
	ldr x2, [x0, #488]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1504, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1504]
	ldr x9, [x0, #1512]
	ldr x10, [x0, #1520]
	ldr x11, [x0, #1528]
	ldr x12, [x0, #1536]
	ldr x13, [x0, #1544]
	ldr x14, [x0, #1552]
	ldr x15, [x0, #1560]
	ldr x21, [x0, #1568]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1504]
	str x9, [x0, #1512]
	str x10, [x0, #1520]
	str x11, [x0, #1528]
	str x12, [x0, #1536]
	str x13, [x0, #1544]
	str x14, [x0, #1552]
	str x15, [x0, #1560]
	str x21, [x0, #1568]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1504]
	ldr x9, [x0, #1512]
	ldr x10, [x0, #1520]
	ldr x11, [x0, #1528]
	ldr x12, [x0, #1536]
	ldr x13, [x0, #1544]
	ldr x14, [x0, #1552]
	ldr x15, [x0, #1560]
	ldr x21, [x0, #1568]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1504]
	str x9, [x0, #1512]
	str x10, [x0, #1520]
	str x11, [x0, #1528]
	str x12, [x0, #1536]
	str x13, [x0, #1544]
	str x14, [x0, #1552]
	str x15, [x0, #1560]
	str x21, [x0, #1568]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1504]
	subs x8, x8, x2
	ldr x2, [x0, #1512]
	sbcs x9, x9, x2
	ldr x2, [x0, #1520]
	sbcs x10, x10, x2
	ldr x2, [x0, #1528]
	sbcs x11, x11, x2
	ldr x2, [x0, #1536]
	sbcs x12, x12, x2
	ldr x2, [x0, #1544]
	sbcs x13, x13, x2
	ldr x2, [x0, #1552]
	sbcs x14, x14, x2
	ldr x2, [x0, #1560]
	sbcs x15, x15, x2
	ldr x2, [x0, #1568]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	mov v29.d[0], x30
	movz x1, #1576, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1144]
	adds x8, x8, x2
	ldr x2, [x0, #1152]
	adcs x9, x9, x2
	ldr x2, [x0, #1160]
	adcs x10, x10, x2
	ldr x2, [x0, #1168]
	adcs x11, x11, x2
	ldr x2, [x0, #1176]
	adcs x12, x12, x2
	ldr x2, [x0, #1184]
	adcs x13, x13, x2
	ldr x2, [x0, #1192]
	adcs x14, x14, x2
	ldr x2, [x0, #1200]
	adcs x15, x15, x2
	ldr x2, [x0, #1208]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1144]
	adds x8, x8, x2
	ldr x2, [x0, #1152]
	adcs x9, x9, x2
	ldr x2, [x0, #1160]
	adcs x10, x10, x2
	ldr x2, [x0, #1168]
	adcs x11, x11, x2
	ldr x2, [x0, #1176]
	adcs x12, x12, x2
	ldr x2, [x0, #1184]
	adcs x13, x13, x2
	ldr x2, [x0, #1192]
	adcs x14, x14, x2
	ldr x2, [x0, #1200]
	adcs x15, x15, x2
	ldr x2, [x0, #1208]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1144]
	adds x8, x8, x2
	ldr x2, [x0, #1152]
	adcs x9, x9, x2
	ldr x2, [x0, #1160]
	adcs x10, x10, x2
	ldr x2, [x0, #1168]
	adcs x11, x11, x2
	ldr x2, [x0, #1176]
	adcs x12, x12, x2
	ldr x2, [x0, #1184]
	adcs x13, x13, x2
	ldr x2, [x0, #1192]
	adcs x14, x14, x2
	ldr x2, [x0, #1200]
	adcs x15, x15, x2
	ldr x2, [x0, #1208]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1576]
	ldr x9, [x0, #1584]
	ldr x10, [x0, #1592]
	ldr x11, [x0, #1600]
	ldr x12, [x0, #1608]
	ldr x13, [x0, #1616]
	ldr x14, [x0, #1624]
	ldr x15, [x0, #1632]
	ldr x21, [x0, #1640]
	ldr x2, [x0, #1144]
	subs x8, x8, x2
	ldr x2, [x0, #1152]
	sbcs x9, x9, x2
	ldr x2, [x0, #1160]
	sbcs x10, x10, x2
	ldr x2, [x0, #1168]
	sbcs x11, x11, x2
	ldr x2, [x0, #1176]
	sbcs x12, x12, x2
	ldr x2, [x0, #1184]
	sbcs x13, x13, x2
	ldr x2, [x0, #1192]
	sbcs x14, x14, x2
	ldr x2, [x0, #1200]
	sbcs x15, x15, x2
	ldr x2, [x0, #1208]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
	movz x7, #0, lsl #0
	ldr x8, [x0, #3160]
	ldr x9, [x0, #3168]
	ldr x10, [x0, #3176]
	ldr x11, [x0, #3184]
	ldr x12, [x0, #3192]
	ldr x13, [x0, #3200]
	ldr x14, [x0, #3208]
	ldr x15, [x0, #3216]
	ldr x21, [x0, #3224]
	ldr x2, [x0, #3160]
	adds x8, x8, x2
	ldr x2, [x0, #3168]
	adcs x9, x9, x2
	ldr x2, [x0, #3176]
	adcs x10, x10, x2
	ldr x2, [x0, #3184]
	adcs x11, x11, x2
	ldr x2, [x0, #3192]
	adcs x12, x12, x2
	ldr x2, [x0, #3200]
	adcs x13, x13, x2
	ldr x2, [x0, #3208]
	adcs x14, x14, x2
	ldr x2, [x0, #3216]
	adcs x15, x15, x2
	ldr x2, [x0, #3224]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	str x21, [x0, #1280]
212:
	movz x7, #0, lsl #0
	ldr x8, [x0, #1504]
	ldr x9, [x0, #1512]
	ldr x10, [x0, #1520]
	ldr x11, [x0, #1528]
	ldr x12, [x0, #1536]
	ldr x13, [x0, #1544]
	ldr x14, [x0, #1552]
	ldr x15, [x0, #1560]
	ldr x21, [x0, #1568]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1720]
	str x9, [x0, #1728]
	str x10, [x0, #1736]
	str x11, [x0, #1744]
	str x12, [x0, #1752]
	str x13, [x0, #1760]
	str x14, [x0, #1768]
	str x15, [x0, #1776]
	str x21, [x0, #1784]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1504, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1576]
	ldr x9, [x0, #1584]
	ldr x10, [x0, #1592]
	ldr x11, [x0, #1600]
	ldr x12, [x0, #1608]
	ldr x13, [x0, #1616]
	ldr x14, [x0, #1624]
	ldr x15, [x0, #1632]
	ldr x21, [x0, #1640]
	ldr x2, [x0, #1144]
	subs x8, x8, x2
	ldr x2, [x0, #1152]
	sbcs x9, x9, x2
	ldr x2, [x0, #1160]
	sbcs x10, x10, x2
	ldr x2, [x0, #1168]
	sbcs x11, x11, x2
	ldr x2, [x0, #1176]
	sbcs x12, x12, x2
	ldr x2, [x0, #1184]
	sbcs x13, x13, x2
	ldr x2, [x0, #1192]
	sbcs x14, x14, x2
	ldr x2, [x0, #1200]
	sbcs x15, x15, x2
	ldr x2, [x0, #1208]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2008]
	str x9, [x0, #2016]
	str x10, [x0, #2024]
	str x11, [x0, #2032]
	str x12, [x0, #2040]
	str x13, [x0, #2048]
	str x14, [x0, #2056]
	str x15, [x0, #2064]
	str x21, [x0, #2072]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #2008, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1504]
	ldr x9, [x0, #1512]
	ldr x10, [x0, #1520]
	ldr x11, [x0, #1528]
	ldr x12, [x0, #1536]
	ldr x13, [x0, #1544]
	ldr x14, [x0, #1552]
	ldr x15, [x0, #1560]
	ldr x21, [x0, #1568]
	ldr x2, [x0, #1936]
	subs x8, x8, x2
	ldr x2, [x0, #1944]
	sbcs x9, x9, x2
	ldr x2, [x0, #1952]
	sbcs x10, x10, x2
	ldr x2, [x0, #1960]
	sbcs x11, x11, x2
	ldr x2, [x0, #1968]
	sbcs x12, x12, x2
	ldr x2, [x0, #1976]
	sbcs x13, x13, x2
	ldr x2, [x0, #1984]
	sbcs x14, x14, x2
	ldr x2, [x0, #1992]
	sbcs x15, x15, x2
	ldr x2, [x0, #2000]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1576, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	ldr x2, [x0, #1504]
	subs x8, x8, x2
	ldr x2, [x0, #1512]
	sbcs x9, x9, x2
	ldr x2, [x0, #1520]
	sbcs x10, x10, x2
	ldr x2, [x0, #1528]
	sbcs x11, x11, x2
	ldr x2, [x0, #1536]
	sbcs x12, x12, x2
	ldr x2, [x0, #1544]
	sbcs x13, x13, x2
	ldr x2, [x0, #1552]
	sbcs x14, x14, x2
	ldr x2, [x0, #1560]
	sbcs x15, x15, x2
	ldr x2, [x0, #1568]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1936]
	subs x8, x8, x2
	ldr x2, [x0, #1944]
	sbcs x9, x9, x2
	ldr x2, [x0, #1952]
	sbcs x10, x10, x2
	ldr x2, [x0, #1960]
	sbcs x11, x11, x2
	ldr x2, [x0, #1968]
	sbcs x12, x12, x2
	ldr x2, [x0, #1976]
	sbcs x13, x13, x2
	ldr x2, [x0, #1984]
	sbcs x14, x14, x2
	ldr x2, [x0, #1992]
	sbcs x15, x15, x2
	ldr x2, [x0, #2000]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1504]
	ldr x9, [x0, #1512]
	ldr x10, [x0, #1520]
	ldr x11, [x0, #1528]
	ldr x12, [x0, #1536]
	ldr x13, [x0, #1544]
	ldr x14, [x0, #1552]
	ldr x15, [x0, #1560]
	ldr x21, [x0, #1568]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	ldr x4, [x0, #1072]
	str x4, [x20, #5176]
	ldr x4, [x0, #1080]
	str x4, [x20, #5184]
	ldr x4, [x0, #1088]
	str x4, [x20, #5192]
	ldr x4, [x0, #1096]
	str x4, [x20, #5200]
	ldr x4, [x0, #1104]
	str x4, [x20, #5208]
	ldr x4, [x0, #1112]
	str x4, [x20, #5216]
	ldr x4, [x0, #1120]
	str x4, [x20, #5224]
	ldr x4, [x0, #1128]
	str x4, [x20, #5232]
	ldr x4, [x0, #1136]
	str x4, [x20, #5240]
	ldr x4, [x0, #1144]
	str x4, [x20, #5248]
	ldr x4, [x0, #1152]
	str x4, [x20, #5256]
	ldr x4, [x0, #1160]
	str x4, [x20, #5264]
	ldr x4, [x0, #1168]
	str x4, [x20, #5272]
	ldr x4, [x0, #1176]
	str x4, [x20, #5280]
	ldr x4, [x0, #1184]
	str x4, [x20, #5288]
	ldr x4, [x0, #1192]
	str x4, [x20, #5296]
	ldr x4, [x0, #1200]
	str x4, [x20, #5304]
	ldr x4, [x0, #1208]
	str x4, [x20, #5312]
	ldr x4, [x0, #1216]
	str x4, [x20, #5320]
	ldr x4, [x0, #1224]
	str x4, [x20, #5328]
	ldr x4, [x0, #1232]
	str x4, [x20, #5336]
	ldr x4, [x0, #1240]
	str x4, [x20, #5344]
	ldr x4, [x0, #1248]
	str x4, [x20, #5352]
	ldr x4, [x0, #1256]
	str x4, [x20, #5360]
	ldr x4, [x0, #1264]
	str x4, [x20, #5368]
	ldr x4, [x0, #1272]
	str x4, [x20, #5376]
	ldr x4, [x0, #1280]
	str x4, [x20, #5384]
	add x20, x20, #216
	sub x19, x19, #1
	cbnz x19, 212b
	ldr x1, [x0, #5320]
	str x1, [x0, #1864]
	ldr x1, [x0, #5328]
	str x1, [x0, #1872]
	ldr x1, [x0, #5336]
	str x1, [x0, #1880]
	ldr x1, [x0, #5344]
	str x1, [x0, #1888]
	ldr x1, [x0, #5352]
	str x1, [x0, #1896]
	ldr x1, [x0, #5360]
	str x1, [x0, #1904]
	ldr x1, [x0, #5368]
	str x1, [x0, #1912]
	ldr x1, [x0, #5376]
	str x1, [x0, #1920]
	ldr x1, [x0, #5384]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #6904]
	ldr x1, [x0, #1728]
	str x1, [x0, #6912]
	ldr x1, [x0, #1736]
	str x1, [x0, #6920]
	ldr x1, [x0, #1744]
	str x1, [x0, #6928]
	ldr x1, [x0, #1752]
	str x1, [x0, #6936]
	ldr x1, [x0, #1760]
	str x1, [x0, #6944]
	ldr x1, [x0, #1768]
	str x1, [x0, #6952]
	ldr x1, [x0, #1776]
	str x1, [x0, #6960]
	ldr x1, [x0, #1784]
	str x1, [x0, #6968]
	ldr x1, [x0, #1792]
	str x1, [x0, #6976]
	ldr x1, [x0, #1800]
	str x1, [x0, #6984]
	ldr x1, [x0, #1808]
	str x1, [x0, #6992]
	ldr x1, [x0, #1816]
	str x1, [x0, #7000]
	ldr x1, [x0, #1824]
	str x1, [x0, #7008]
	ldr x1, [x0, #1832]
	str x1, [x0, #7016]
	ldr x1, [x0, #1840]
	str x1, [x0, #7024]
	ldr x1, [x0, #1848]
	str x1, [x0, #7032]
	ldr x1, [x0, #1856]
	str x1, [x0, #7040]
	ldr x1, [x0, #5536]
	str x1, [x0, #1864]
	ldr x1, [x0, #5544]
	str x1, [x0, #1872]
	ldr x1, [x0, #5552]
	str x1, [x0, #1880]
	ldr x1, [x0, #5560]
	str x1, [x0, #1888]
	ldr x1, [x0, #5568]
	str x1, [x0, #1896]
	ldr x1, [x0, #5576]
	str x1, [x0, #1904]
	ldr x1, [x0, #5584]
	str x1, [x0, #1912]
	ldr x1, [x0, #5592]
	str x1, [x0, #1920]
	ldr x1, [x0, #5600]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7048]
	ldr x1, [x0, #1728]
	str x1, [x0, #7056]
	ldr x1, [x0, #1736]
	str x1, [x0, #7064]
	ldr x1, [x0, #1744]
	str x1, [x0, #7072]
	ldr x1, [x0, #1752]
	str x1, [x0, #7080]
	ldr x1, [x0, #1760]
	str x1, [x0, #7088]
	ldr x1, [x0, #1768]
	str x1, [x0, #7096]
	ldr x1, [x0, #1776]
	str x1, [x0, #7104]
	ldr x1, [x0, #1784]
	str x1, [x0, #7112]
	ldr x1, [x0, #1792]
	str x1, [x0, #7120]
	ldr x1, [x0, #1800]
	str x1, [x0, #7128]
	ldr x1, [x0, #1808]
	str x1, [x0, #7136]
	ldr x1, [x0, #1816]
	str x1, [x0, #7144]
	ldr x1, [x0, #1824]
	str x1, [x0, #7152]
	ldr x1, [x0, #1832]
	str x1, [x0, #7160]
	ldr x1, [x0, #1840]
	str x1, [x0, #7168]
	ldr x1, [x0, #1848]
	str x1, [x0, #7176]
	ldr x1, [x0, #1856]
	str x1, [x0, #7184]
	ldr x1, [x0, #5752]
	str x1, [x0, #1864]
	ldr x1, [x0, #5760]
	str x1, [x0, #1872]
	ldr x1, [x0, #5768]
	str x1, [x0, #1880]
	ldr x1, [x0, #5776]
	str x1, [x0, #1888]
	ldr x1, [x0, #5784]
	str x1, [x0, #1896]
	ldr x1, [x0, #5792]
	str x1, [x0, #1904]
	ldr x1, [x0, #5800]
	str x1, [x0, #1912]
	ldr x1, [x0, #5808]
	str x1, [x0, #1920]
	ldr x1, [x0, #5816]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7192]
	ldr x1, [x0, #1728]
	str x1, [x0, #7200]
	ldr x1, [x0, #1736]
	str x1, [x0, #7208]
	ldr x1, [x0, #1744]
	str x1, [x0, #7216]
	ldr x1, [x0, #1752]
	str x1, [x0, #7224]
	ldr x1, [x0, #1760]
	str x1, [x0, #7232]
	ldr x1, [x0, #1768]
	str x1, [x0, #7240]
	ldr x1, [x0, #1776]
	str x1, [x0, #7248]
	ldr x1, [x0, #1784]
	str x1, [x0, #7256]
	ldr x1, [x0, #1792]
	str x1, [x0, #7264]
	ldr x1, [x0, #1800]
	str x1, [x0, #7272]
	ldr x1, [x0, #1808]
	str x1, [x0, #7280]
	ldr x1, [x0, #1816]
	str x1, [x0, #7288]
	ldr x1, [x0, #1824]
	str x1, [x0, #7296]
	ldr x1, [x0, #1832]
	str x1, [x0, #7304]
	ldr x1, [x0, #1840]
	str x1, [x0, #7312]
	ldr x1, [x0, #1848]
	str x1, [x0, #7320]
	ldr x1, [x0, #1856]
	str x1, [x0, #7328]
	ldr x1, [x0, #5968]
	str x1, [x0, #1864]
	ldr x1, [x0, #5976]
	str x1, [x0, #1872]
	ldr x1, [x0, #5984]
	str x1, [x0, #1880]
	ldr x1, [x0, #5992]
	str x1, [x0, #1888]
	ldr x1, [x0, #6000]
	str x1, [x0, #1896]
	ldr x1, [x0, #6008]
	str x1, [x0, #1904]
	ldr x1, [x0, #6016]
	str x1, [x0, #1912]
	ldr x1, [x0, #6024]
	str x1, [x0, #1920]
	ldr x1, [x0, #6032]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7336]
	ldr x1, [x0, #1728]
	str x1, [x0, #7344]
	ldr x1, [x0, #1736]
	str x1, [x0, #7352]
	ldr x1, [x0, #1744]
	str x1, [x0, #7360]
	ldr x1, [x0, #1752]
	str x1, [x0, #7368]
	ldr x1, [x0, #1760]
	str x1, [x0, #7376]
	ldr x1, [x0, #1768]
	str x1, [x0, #7384]
	ldr x1, [x0, #1776]
	str x1, [x0, #7392]
	ldr x1, [x0, #1784]
	str x1, [x0, #7400]
	ldr x1, [x0, #1792]
	str x1, [x0, #7408]
	ldr x1, [x0, #1800]
	str x1, [x0, #7416]
	ldr x1, [x0, #1808]
	str x1, [x0, #7424]
	ldr x1, [x0, #1816]
	str x1, [x0, #7432]
	ldr x1, [x0, #1824]
	str x1, [x0, #7440]
	ldr x1, [x0, #1832]
	str x1, [x0, #7448]
	ldr x1, [x0, #1840]
	str x1, [x0, #7456]
	ldr x1, [x0, #1848]
	str x1, [x0, #7464]
	ldr x1, [x0, #1856]
	str x1, [x0, #7472]
	ldr x1, [x0, #6184]
	str x1, [x0, #1864]
	ldr x1, [x0, #6192]
	str x1, [x0, #1872]
	ldr x1, [x0, #6200]
	str x1, [x0, #1880]
	ldr x1, [x0, #6208]
	str x1, [x0, #1888]
	ldr x1, [x0, #6216]
	str x1, [x0, #1896]
	ldr x1, [x0, #6224]
	str x1, [x0, #1904]
	ldr x1, [x0, #6232]
	str x1, [x0, #1912]
	ldr x1, [x0, #6240]
	str x1, [x0, #1920]
	ldr x1, [x0, #6248]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7480]
	ldr x1, [x0, #1728]
	str x1, [x0, #7488]
	ldr x1, [x0, #1736]
	str x1, [x0, #7496]
	ldr x1, [x0, #1744]
	str x1, [x0, #7504]
	ldr x1, [x0, #1752]
	str x1, [x0, #7512]
	ldr x1, [x0, #1760]
	str x1, [x0, #7520]
	ldr x1, [x0, #1768]
	str x1, [x0, #7528]
	ldr x1, [x0, #1776]
	str x1, [x0, #7536]
	ldr x1, [x0, #1784]
	str x1, [x0, #7544]
	ldr x1, [x0, #1792]
	str x1, [x0, #7552]
	ldr x1, [x0, #1800]
	str x1, [x0, #7560]
	ldr x1, [x0, #1808]
	str x1, [x0, #7568]
	ldr x1, [x0, #1816]
	str x1, [x0, #7576]
	ldr x1, [x0, #1824]
	str x1, [x0, #7584]
	ldr x1, [x0, #1832]
	str x1, [x0, #7592]
	ldr x1, [x0, #1840]
	str x1, [x0, #7600]
	ldr x1, [x0, #1848]
	str x1, [x0, #7608]
	ldr x1, [x0, #1856]
	str x1, [x0, #7616]
	ldr x1, [x0, #6400]
	str x1, [x0, #1864]
	ldr x1, [x0, #6408]
	str x1, [x0, #1872]
	ldr x1, [x0, #6416]
	str x1, [x0, #1880]
	ldr x1, [x0, #6424]
	str x1, [x0, #1888]
	ldr x1, [x0, #6432]
	str x1, [x0, #1896]
	ldr x1, [x0, #6440]
	str x1, [x0, #1904]
	ldr x1, [x0, #6448]
	str x1, [x0, #1912]
	ldr x1, [x0, #6456]
	str x1, [x0, #1920]
	ldr x1, [x0, #6464]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7624]
	ldr x1, [x0, #1728]
	str x1, [x0, #7632]
	ldr x1, [x0, #1736]
	str x1, [x0, #7640]
	ldr x1, [x0, #1744]
	str x1, [x0, #7648]
	ldr x1, [x0, #1752]
	str x1, [x0, #7656]
	ldr x1, [x0, #1760]
	str x1, [x0, #7664]
	ldr x1, [x0, #1768]
	str x1, [x0, #7672]
	ldr x1, [x0, #1776]
	str x1, [x0, #7680]
	ldr x1, [x0, #1784]
	str x1, [x0, #7688]
	ldr x1, [x0, #1792]
	str x1, [x0, #7696]
	ldr x1, [x0, #1800]
	str x1, [x0, #7704]
	ldr x1, [x0, #1808]
	str x1, [x0, #7712]
	ldr x1, [x0, #1816]
	str x1, [x0, #7720]
	ldr x1, [x0, #1824]
	str x1, [x0, #7728]
	ldr x1, [x0, #1832]
	str x1, [x0, #7736]
	ldr x1, [x0, #1840]
	str x1, [x0, #7744]
	ldr x1, [x0, #1848]
	str x1, [x0, #7752]
	ldr x1, [x0, #1856]
	str x1, [x0, #7760]
	ldr x1, [x0, #6616]
	str x1, [x0, #1864]
	ldr x1, [x0, #6624]
	str x1, [x0, #1872]
	ldr x1, [x0, #6632]
	str x1, [x0, #1880]
	ldr x1, [x0, #6640]
	str x1, [x0, #1888]
	ldr x1, [x0, #6648]
	str x1, [x0, #1896]
	ldr x1, [x0, #6656]
	str x1, [x0, #1904]
	ldr x1, [x0, #6664]
	str x1, [x0, #1912]
	ldr x1, [x0, #6672]
	str x1, [x0, #1920]
	ldr x1, [x0, #6680]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7768]
	ldr x1, [x0, #1728]
	str x1, [x0, #7776]
	ldr x1, [x0, #1736]
	str x1, [x0, #7784]
	ldr x1, [x0, #1744]
	str x1, [x0, #7792]
	ldr x1, [x0, #1752]
	str x1, [x0, #7800]
	ldr x1, [x0, #1760]
	str x1, [x0, #7808]
	ldr x1, [x0, #1768]
	str x1, [x0, #7816]
	ldr x1, [x0, #1776]
	str x1, [x0, #7824]
	ldr x1, [x0, #1784]
	str x1, [x0, #7832]
	ldr x1, [x0, #1792]
	str x1, [x0, #7840]
	ldr x1, [x0, #1800]
	str x1, [x0, #7848]
	ldr x1, [x0, #1808]
	str x1, [x0, #7856]
	ldr x1, [x0, #1816]
	str x1, [x0, #7864]
	ldr x1, [x0, #1824]
	str x1, [x0, #7872]
	ldr x1, [x0, #1832]
	str x1, [x0, #7880]
	ldr x1, [x0, #1840]
	str x1, [x0, #7888]
	ldr x1, [x0, #1848]
	str x1, [x0, #7896]
	ldr x1, [x0, #1856]
	str x1, [x0, #7904]
	ldr x1, [x0, #6832]
	str x1, [x0, #1864]
	ldr x1, [x0, #6840]
	str x1, [x0, #1872]
	ldr x1, [x0, #6848]
	str x1, [x0, #1880]
	ldr x1, [x0, #6856]
	str x1, [x0, #1888]
	ldr x1, [x0, #6864]
	str x1, [x0, #1896]
	ldr x1, [x0, #6872]
	str x1, [x0, #1904]
	ldr x1, [x0, #6880]
	str x1, [x0, #1912]
	ldr x1, [x0, #6888]
	str x1, [x0, #1920]
	ldr x1, [x0, #6896]
	str x1, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1864, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1720]
	str x1, [x0, #7912]
	ldr x1, [x0, #1728]
	str x1, [x0, #7920]
	ldr x1, [x0, #1736]
	str x1, [x0, #7928]
	ldr x1, [x0, #1744]
	str x1, [x0, #7936]
	ldr x1, [x0, #1752]
	str x1, [x0, #7944]
	ldr x1, [x0, #1760]
	str x1, [x0, #7952]
	ldr x1, [x0, #1768]
	str x1, [x0, #7960]
	ldr x1, [x0, #1776]
	str x1, [x0, #7968]
	ldr x1, [x0, #1784]
	str x1, [x0, #7976]
	ldr x1, [x0, #1792]
	str x1, [x0, #7984]
	ldr x1, [x0, #1800]
	str x1, [x0, #7992]
	ldr x1, [x0, #1808]
	str x1, [x0, #8000]
	ldr x1, [x0, #1816]
	str x1, [x0, #8008]
	ldr x1, [x0, #1824]
	str x1, [x0, #8016]
	ldr x1, [x0, #1832]
	str x1, [x0, #8024]
	ldr x1, [x0, #1840]
	str x1, [x0, #8032]
	ldr x1, [x0, #1848]
	str x1, [x0, #8040]
	ldr x1, [x0, #1856]
	str x1, [x0, #8048]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1376]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1488]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1496]
	movz x19, #576, lsl #0
	add x16, x0, x19
	ldrb w2, [x16, #4024]
	cbnz x2, 213f
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
	b 214f
213:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x17, #144, lsl #0
	mul x17, x2, x17
	add x16, x0, x17
	ldr x4, [x16, #6904]
	str x4, [x0, #1144]
	ldr x4, [x16, #6912]
	str x4, [x0, #1152]
	ldr x4, [x16, #6920]
	str x4, [x0, #1160]
	ldr x4, [x16, #6928]
	str x4, [x0, #1168]
	ldr x4, [x16, #6936]
	str x4, [x0, #1176]
	ldr x4, [x16, #6944]
	str x4, [x0, #1184]
	ldr x4, [x16, #6952]
	str x4, [x0, #1192]
	ldr x4, [x16, #6960]
	str x4, [x0, #1200]
	ldr x4, [x16, #6968]
	str x4, [x0, #1208]
	ldr x4, [x16, #6976]
	str x4, [x0, #1216]
	ldr x4, [x16, #6984]
	str x4, [x0, #1224]
	ldr x4, [x16, #6992]
	str x4, [x0, #1232]
	ldr x4, [x16, #7000]
	str x4, [x0, #1240]
	ldr x4, [x16, #7008]
	str x4, [x0, #1248]
	ldr x4, [x16, #7016]
	str x4, [x0, #1256]
	ldr x4, [x16, #7024]
	str x4, [x0, #1264]
	ldr x4, [x16, #7032]
	str x4, [x0, #1272]
	ldr x4, [x16, #7040]
	str x4, [x0, #1280]
	movz x17, #216, lsl #0
	mul x2, x2, x17
	add x16, x0, x2
	ldr x4, [x16, #5176]
	str x4, [x0, #1504]
	ldr x4, [x16, #5184]
	str x4, [x0, #1512]
	ldr x4, [x16, #5192]
	str x4, [x0, #1520]
	ldr x4, [x16, #5200]
	str x4, [x0, #1528]
	ldr x4, [x16, #5208]
	str x4, [x0, #1536]
	ldr x4, [x16, #5216]
	str x4, [x0, #1544]
	ldr x4, [x16, #5224]
	str x4, [x0, #1552]
	ldr x4, [x16, #5232]
	str x4, [x0, #1560]
	ldr x4, [x16, #5240]
	str x4, [x0, #1568]
	ldr x4, [x16, #5248]
	str x4, [x0, #1576]
	ldr x4, [x16, #5256]
	str x4, [x0, #1584]
	ldr x4, [x16, #5264]
	str x4, [x0, #1592]
	ldr x4, [x16, #5272]
	str x4, [x0, #1600]
	ldr x4, [x16, #5280]
	str x4, [x0, #1608]
	ldr x4, [x16, #5288]
	str x4, [x0, #1616]
	ldr x4, [x16, #5296]
	str x4, [x0, #1624]
	ldr x4, [x16, #5304]
	str x4, [x0, #1632]
	ldr x4, [x16, #5312]
	str x4, [x0, #1640]
	ldr x4, [x16, #5320]
	str x4, [x0, #1648]
	ldr x4, [x16, #5328]
	str x4, [x0, #1656]
	ldr x4, [x16, #5336]
	str x4, [x0, #1664]
	ldr x4, [x16, #5344]
	str x4, [x0, #1672]
	ldr x4, [x16, #5352]
	str x4, [x0, #1680]
	ldr x4, [x16, #5360]
	str x4, [x0, #1688]
	ldr x4, [x16, #5368]
	str x4, [x0, #1696]
	ldr x4, [x16, #5376]
	str x4, [x0, #1704]
	ldr x4, [x16, #5384]
	str x4, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #4024]
	lsr x3, x3, #7
	cbnz x3, 215f
	b 216f
215:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
216:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1432]
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	ldr x2, [x0, #1456]
	orr x1, x1, x2
	ldr x2, [x0, #1464]
	orr x1, x1, x2
	ldr x2, [x0, #1472]
	orr x1, x1, x2
	ldr x2, [x0, #1480]
	orr x1, x1, x2
	ldr x2, [x0, #1488]
	orr x1, x1, x2
	ldr x2, [x0, #1496]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 217f
	movz x7, #0, lsl #0
	ldr x1, [x0, #1648]
	ldr x2, [x0, #1656]
	orr x1, x1, x2
	ldr x2, [x0, #1664]
	orr x1, x1, x2
	ldr x2, [x0, #1672]
	orr x1, x1, x2
	ldr x2, [x0, #1680]
	orr x1, x1, x2
	ldr x2, [x0, #1688]
	orr x1, x1, x2
	ldr x2, [x0, #1696]
	orr x1, x1, x2
	ldr x2, [x0, #1704]
	orr x1, x1, x2
	ldr x2, [x0, #1712]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 219f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 221f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	b 222f
221:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 223f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1080]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1088]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1096]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1104]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1120]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1128]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	b 224f
223:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x21, [x0, #1280]
	ldr x2, [x0, #1216]
	adds x8, x8, x2
	ldr x2, [x0, #1224]
	adcs x9, x9, x2
	ldr x2, [x0, #1232]
	adcs x10, x10, x2
	ldr x2, [x0, #1240]
	adcs x11, x11, x2
	ldr x2, [x0, #1248]
	adcs x12, x12, x2
	ldr x2, [x0, #1256]
	adcs x13, x13, x2
	ldr x2, [x0, #1264]
	adcs x14, x14, x2
	ldr x2, [x0, #1272]
	adcs x15, x15, x2
	ldr x2, [x0, #1280]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	str x21, [x0, #1280]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
224:
222:
	b 220f
219:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
220:
	b 218f
217:
	ldr x1, [x0, #1504]
	str x1, [x0, #1072]
	ldr x1, [x0, #1512]
	str x1, [x0, #1080]
	ldr x1, [x0, #1520]
	str x1, [x0, #1088]
	ldr x1, [x0, #1528]
	str x1, [x0, #1096]
	ldr x1, [x0, #1536]
	str x1, [x0, #1104]
	ldr x1, [x0, #1544]
	str x1, [x0, #1112]
	ldr x1, [x0, #1552]
	str x1, [x0, #1120]
	ldr x1, [x0, #1560]
	str x1, [x0, #1128]
	ldr x1, [x0, #1568]
	str x1, [x0, #1136]
	ldr x1, [x0, #1576]
	str x1, [x0, #1144]
	ldr x1, [x0, #1584]
	str x1, [x0, #1152]
	ldr x1, [x0, #1592]
	str x1, [x0, #1160]
	ldr x1, [x0, #1600]
	str x1, [x0, #1168]
	ldr x1, [x0, #1608]
	str x1, [x0, #1176]
	ldr x1, [x0, #1616]
	str x1, [x0, #1184]
	ldr x1, [x0, #1624]
	str x1, [x0, #1192]
	ldr x1, [x0, #1632]
	str x1, [x0, #1200]
	ldr x1, [x0, #1640]
	str x1, [x0, #1208]
	ldr x1, [x0, #1648]
	str x1, [x0, #1216]
	ldr x1, [x0, #1656]
	str x1, [x0, #1224]
	ldr x1, [x0, #1664]
	str x1, [x0, #1232]
	ldr x1, [x0, #1672]
	str x1, [x0, #1240]
	ldr x1, [x0, #1680]
	str x1, [x0, #1248]
	ldr x1, [x0, #1688]
	str x1, [x0, #1256]
	ldr x1, [x0, #1696]
	str x1, [x0, #1264]
	ldr x1, [x0, #1704]
	str x1, [x0, #1272]
	ldr x1, [x0, #1712]
	str x1, [x0, #1280]
218:
214:
	add x16, x0, x19
	ldrb w2, [x16, #3304]
	cbnz x2, 225f
	b 226f
225:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	lsl x2, x2, #1
	sub x2, x2, #2
	movz x3, #144, lsl #0
	mul x2, x2, x3
	adrp x16, {VG_P521_COMB}
	add x16, x16, {VG_P521_COMB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #1504]
	ldr x4, [x16, #8]
	str x4, [x0, #1512]
	ldr x4, [x16, #16]
	str x4, [x0, #1520]
	ldr x4, [x16, #24]
	str x4, [x0, #1528]
	ldr x4, [x16, #32]
	str x4, [x0, #1536]
	ldr x4, [x16, #40]
	str x4, [x0, #1544]
	ldr x4, [x16, #48]
	str x4, [x0, #1552]
	ldr x4, [x16, #56]
	str x4, [x0, #1560]
	ldr x4, [x16, #64]
	str x4, [x0, #1568]
	ldr x4, [x16, #72]
	str x4, [x0, #1576]
	ldr x4, [x16, #80]
	str x4, [x0, #1584]
	ldr x4, [x16, #88]
	str x4, [x0, #1592]
	ldr x4, [x16, #96]
	str x4, [x0, #1600]
	ldr x4, [x16, #104]
	str x4, [x0, #1608]
	ldr x4, [x16, #112]
	str x4, [x0, #1616]
	ldr x4, [x16, #120]
	str x4, [x0, #1624]
	ldr x4, [x16, #128]
	str x4, [x0, #1632]
	ldr x4, [x16, #136]
	str x4, [x0, #1640]
	ldr x1, [x0, #424]
	str x1, [x0, #1648]
	ldr x1, [x0, #432]
	str x1, [x0, #1656]
	ldr x1, [x0, #440]
	str x1, [x0, #1664]
	ldr x1, [x0, #448]
	str x1, [x0, #1672]
	ldr x1, [x0, #456]
	str x1, [x0, #1680]
	ldr x1, [x0, #464]
	str x1, [x0, #1688]
	ldr x1, [x0, #472]
	str x1, [x0, #1696]
	ldr x1, [x0, #480]
	str x1, [x0, #1704]
	ldr x1, [x0, #488]
	str x1, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #3304]
	lsr x3, x3, #7
	cbnz x3, 227f
	b 228f
227:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
228:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1224]
	orr x1, x1, x2
	ldr x2, [x0, #1232]
	orr x1, x1, x2
	ldr x2, [x0, #1240]
	orr x1, x1, x2
	ldr x2, [x0, #1248]
	orr x1, x1, x2
	ldr x2, [x0, #1256]
	orr x1, x1, x2
	ldr x2, [x0, #1264]
	orr x1, x1, x2
	ldr x2, [x0, #1272]
	orr x1, x1, x2
	ldr x2, [x0, #1280]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 229f
	ldr x1, [x0, #1072]
	str x1, [x0, #1864]
	ldr x1, [x0, #1080]
	str x1, [x0, #1872]
	ldr x1, [x0, #1088]
	str x1, [x0, #1880]
	ldr x1, [x0, #1096]
	str x1, [x0, #1888]
	ldr x1, [x0, #1104]
	str x1, [x0, #1896]
	ldr x1, [x0, #1112]
	str x1, [x0, #1904]
	ldr x1, [x0, #1120]
	str x1, [x0, #1912]
	ldr x1, [x0, #1128]
	str x1, [x0, #1920]
	ldr x1, [x0, #1136]
	str x1, [x0, #1928]
	ldr x1, [x0, #1144]
	str x1, [x0, #2008]
	ldr x1, [x0, #1152]
	str x1, [x0, #2016]
	ldr x1, [x0, #1160]
	str x1, [x0, #2024]
	ldr x1, [x0, #1168]
	str x1, [x0, #2032]
	ldr x1, [x0, #1176]
	str x1, [x0, #2040]
	ldr x1, [x0, #1184]
	str x1, [x0, #2048]
	ldr x1, [x0, #1192]
	str x1, [x0, #2056]
	ldr x1, [x0, #1200]
	str x1, [x0, #2064]
	ldr x1, [x0, #1208]
	str x1, [x0, #2072]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 231f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	b 232f
231:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 233f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1376]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1488]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1496]
	b 234f
233:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1288, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1432]
	ldr x9, [x0, #1440]
	ldr x10, [x0, #1448]
	ldr x11, [x0, #1456]
	ldr x12, [x0, #1464]
	ldr x13, [x0, #1472]
	ldr x14, [x0, #1480]
	ldr x15, [x0, #1488]
	ldr x21, [x0, #1496]
	ldr x2, [x0, #1432]
	adds x8, x8, x2
	ldr x2, [x0, #1440]
	adcs x9, x9, x2
	ldr x2, [x0, #1448]
	adcs x10, x10, x2
	ldr x2, [x0, #1456]
	adcs x11, x11, x2
	ldr x2, [x0, #1464]
	adcs x12, x12, x2
	ldr x2, [x0, #1472]
	adcs x13, x13, x2
	ldr x2, [x0, #1480]
	adcs x14, x14, x2
	ldr x2, [x0, #1488]
	adcs x15, x15, x2
	ldr x2, [x0, #1496]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
234:
232:
	b 230f
229:
	ldr x1, [x0, #1504]
	str x1, [x0, #1288]
	ldr x1, [x0, #1512]
	str x1, [x0, #1296]
	ldr x1, [x0, #1520]
	str x1, [x0, #1304]
	ldr x1, [x0, #1528]
	str x1, [x0, #1312]
	ldr x1, [x0, #1536]
	str x1, [x0, #1320]
	ldr x1, [x0, #1544]
	str x1, [x0, #1328]
	ldr x1, [x0, #1552]
	str x1, [x0, #1336]
	ldr x1, [x0, #1560]
	str x1, [x0, #1344]
	ldr x1, [x0, #1568]
	str x1, [x0, #1352]
	ldr x1, [x0, #1576]
	str x1, [x0, #1360]
	ldr x1, [x0, #1584]
	str x1, [x0, #1368]
	ldr x1, [x0, #1592]
	str x1, [x0, #1376]
	ldr x1, [x0, #1600]
	str x1, [x0, #1384]
	ldr x1, [x0, #1608]
	str x1, [x0, #1392]
	ldr x1, [x0, #1616]
	str x1, [x0, #1400]
	ldr x1, [x0, #1624]
	str x1, [x0, #1408]
	ldr x1, [x0, #1632]
	str x1, [x0, #1416]
	ldr x1, [x0, #1640]
	str x1, [x0, #1424]
	ldr x1, [x0, #1648]
	str x1, [x0, #1432]
	ldr x1, [x0, #1656]
	str x1, [x0, #1440]
	ldr x1, [x0, #1664]
	str x1, [x0, #1448]
	ldr x1, [x0, #1672]
	str x1, [x0, #1456]
	ldr x1, [x0, #1680]
	str x1, [x0, #1464]
	ldr x1, [x0, #1688]
	str x1, [x0, #1472]
	ldr x1, [x0, #1696]
	str x1, [x0, #1480]
	ldr x1, [x0, #1704]
	str x1, [x0, #1488]
	ldr x1, [x0, #1712]
	str x1, [x0, #1496]
230:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
226:
235:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1288, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1216]
	adds x8, x8, x2
	ldr x2, [x0, #1224]
	adcs x9, x9, x2
	ldr x2, [x0, #1232]
	adcs x10, x10, x2
	ldr x2, [x0, #1240]
	adcs x11, x11, x2
	ldr x2, [x0, #1248]
	adcs x12, x12, x2
	ldr x2, [x0, #1256]
	adcs x13, x13, x2
	ldr x2, [x0, #1264]
	adcs x14, x14, x2
	ldr x2, [x0, #1272]
	adcs x15, x15, x2
	ldr x2, [x0, #1280]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1432]
	ldr x9, [x0, #1440]
	ldr x10, [x0, #1448]
	ldr x11, [x0, #1456]
	ldr x12, [x0, #1464]
	ldr x13, [x0, #1472]
	ldr x14, [x0, #1480]
	ldr x15, [x0, #1488]
	ldr x21, [x0, #1496]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1432]
	ldr x9, [x0, #1440]
	ldr x10, [x0, #1448]
	ldr x11, [x0, #1456]
	ldr x12, [x0, #1464]
	ldr x13, [x0, #1472]
	ldr x14, [x0, #1480]
	ldr x15, [x0, #1488]
	ldr x21, [x0, #1496]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	add x16, x0, x19
	ldrb w2, [x16, #4024]
	cbnz x2, 236f
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
	b 237f
236:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x17, #144, lsl #0
	mul x17, x2, x17
	add x16, x0, x17
	ldr x4, [x16, #6904]
	str x4, [x0, #1144]
	ldr x4, [x16, #6912]
	str x4, [x0, #1152]
	ldr x4, [x16, #6920]
	str x4, [x0, #1160]
	ldr x4, [x16, #6928]
	str x4, [x0, #1168]
	ldr x4, [x16, #6936]
	str x4, [x0, #1176]
	ldr x4, [x16, #6944]
	str x4, [x0, #1184]
	ldr x4, [x16, #6952]
	str x4, [x0, #1192]
	ldr x4, [x16, #6960]
	str x4, [x0, #1200]
	ldr x4, [x16, #6968]
	str x4, [x0, #1208]
	ldr x4, [x16, #6976]
	str x4, [x0, #1216]
	ldr x4, [x16, #6984]
	str x4, [x0, #1224]
	ldr x4, [x16, #6992]
	str x4, [x0, #1232]
	ldr x4, [x16, #7000]
	str x4, [x0, #1240]
	ldr x4, [x16, #7008]
	str x4, [x0, #1248]
	ldr x4, [x16, #7016]
	str x4, [x0, #1256]
	ldr x4, [x16, #7024]
	str x4, [x0, #1264]
	ldr x4, [x16, #7032]
	str x4, [x0, #1272]
	ldr x4, [x16, #7040]
	str x4, [x0, #1280]
	movz x17, #216, lsl #0
	mul x2, x2, x17
	add x16, x0, x2
	ldr x4, [x16, #5176]
	str x4, [x0, #1504]
	ldr x4, [x16, #5184]
	str x4, [x0, #1512]
	ldr x4, [x16, #5192]
	str x4, [x0, #1520]
	ldr x4, [x16, #5200]
	str x4, [x0, #1528]
	ldr x4, [x16, #5208]
	str x4, [x0, #1536]
	ldr x4, [x16, #5216]
	str x4, [x0, #1544]
	ldr x4, [x16, #5224]
	str x4, [x0, #1552]
	ldr x4, [x16, #5232]
	str x4, [x0, #1560]
	ldr x4, [x16, #5240]
	str x4, [x0, #1568]
	ldr x4, [x16, #5248]
	str x4, [x0, #1576]
	ldr x4, [x16, #5256]
	str x4, [x0, #1584]
	ldr x4, [x16, #5264]
	str x4, [x0, #1592]
	ldr x4, [x16, #5272]
	str x4, [x0, #1600]
	ldr x4, [x16, #5280]
	str x4, [x0, #1608]
	ldr x4, [x16, #5288]
	str x4, [x0, #1616]
	ldr x4, [x16, #5296]
	str x4, [x0, #1624]
	ldr x4, [x16, #5304]
	str x4, [x0, #1632]
	ldr x4, [x16, #5312]
	str x4, [x0, #1640]
	ldr x4, [x16, #5320]
	str x4, [x0, #1648]
	ldr x4, [x16, #5328]
	str x4, [x0, #1656]
	ldr x4, [x16, #5336]
	str x4, [x0, #1664]
	ldr x4, [x16, #5344]
	str x4, [x0, #1672]
	ldr x4, [x16, #5352]
	str x4, [x0, #1680]
	ldr x4, [x16, #5360]
	str x4, [x0, #1688]
	ldr x4, [x16, #5368]
	str x4, [x0, #1696]
	ldr x4, [x16, #5376]
	str x4, [x0, #1704]
	ldr x4, [x16, #5384]
	str x4, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #4024]
	lsr x3, x3, #7
	cbnz x3, 238f
	b 239f
238:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
239:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1432]
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	ldr x2, [x0, #1456]
	orr x1, x1, x2
	ldr x2, [x0, #1464]
	orr x1, x1, x2
	ldr x2, [x0, #1472]
	orr x1, x1, x2
	ldr x2, [x0, #1480]
	orr x1, x1, x2
	ldr x2, [x0, #1488]
	orr x1, x1, x2
	ldr x2, [x0, #1496]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 240f
	movz x7, #0, lsl #0
	ldr x1, [x0, #1648]
	ldr x2, [x0, #1656]
	orr x1, x1, x2
	ldr x2, [x0, #1664]
	orr x1, x1, x2
	ldr x2, [x0, #1672]
	orr x1, x1, x2
	ldr x2, [x0, #1680]
	orr x1, x1, x2
	ldr x2, [x0, #1688]
	orr x1, x1, x2
	ldr x2, [x0, #1696]
	orr x1, x1, x2
	ldr x2, [x0, #1704]
	orr x1, x1, x2
	ldr x2, [x0, #1712]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 242f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 244f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	b 245f
244:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 246f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1080]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1088]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1096]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1104]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1120]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1128]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	b 247f
246:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x21, [x0, #1280]
	ldr x2, [x0, #1216]
	adds x8, x8, x2
	ldr x2, [x0, #1224]
	adcs x9, x9, x2
	ldr x2, [x0, #1232]
	adcs x10, x10, x2
	ldr x2, [x0, #1240]
	adcs x11, x11, x2
	ldr x2, [x0, #1248]
	adcs x12, x12, x2
	ldr x2, [x0, #1256]
	adcs x13, x13, x2
	ldr x2, [x0, #1264]
	adcs x14, x14, x2
	ldr x2, [x0, #1272]
	adcs x15, x15, x2
	ldr x2, [x0, #1280]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	str x21, [x0, #1280]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
247:
245:
	b 243f
242:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
243:
	b 241f
240:
	ldr x1, [x0, #1504]
	str x1, [x0, #1072]
	ldr x1, [x0, #1512]
	str x1, [x0, #1080]
	ldr x1, [x0, #1520]
	str x1, [x0, #1088]
	ldr x1, [x0, #1528]
	str x1, [x0, #1096]
	ldr x1, [x0, #1536]
	str x1, [x0, #1104]
	ldr x1, [x0, #1544]
	str x1, [x0, #1112]
	ldr x1, [x0, #1552]
	str x1, [x0, #1120]
	ldr x1, [x0, #1560]
	str x1, [x0, #1128]
	ldr x1, [x0, #1568]
	str x1, [x0, #1136]
	ldr x1, [x0, #1576]
	str x1, [x0, #1144]
	ldr x1, [x0, #1584]
	str x1, [x0, #1152]
	ldr x1, [x0, #1592]
	str x1, [x0, #1160]
	ldr x1, [x0, #1600]
	str x1, [x0, #1168]
	ldr x1, [x0, #1608]
	str x1, [x0, #1176]
	ldr x1, [x0, #1616]
	str x1, [x0, #1184]
	ldr x1, [x0, #1624]
	str x1, [x0, #1192]
	ldr x1, [x0, #1632]
	str x1, [x0, #1200]
	ldr x1, [x0, #1640]
	str x1, [x0, #1208]
	ldr x1, [x0, #1648]
	str x1, [x0, #1216]
	ldr x1, [x0, #1656]
	str x1, [x0, #1224]
	ldr x1, [x0, #1664]
	str x1, [x0, #1232]
	ldr x1, [x0, #1672]
	str x1, [x0, #1240]
	ldr x1, [x0, #1680]
	str x1, [x0, #1248]
	ldr x1, [x0, #1688]
	str x1, [x0, #1256]
	ldr x1, [x0, #1696]
	str x1, [x0, #1264]
	ldr x1, [x0, #1704]
	str x1, [x0, #1272]
	ldr x1, [x0, #1712]
	str x1, [x0, #1280]
241:
237:
	add x16, x0, x19
	ldrb w2, [x16, #3304]
	cbnz x2, 248f
	b 249f
248:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	lsl x2, x2, #1
	sub x2, x2, #2
	movz x3, #144, lsl #0
	mul x2, x2, x3
	adrp x16, {VG_P521_COMB}
	add x16, x16, {VG_P521_COMB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #1504]
	ldr x4, [x16, #8]
	str x4, [x0, #1512]
	ldr x4, [x16, #16]
	str x4, [x0, #1520]
	ldr x4, [x16, #24]
	str x4, [x0, #1528]
	ldr x4, [x16, #32]
	str x4, [x0, #1536]
	ldr x4, [x16, #40]
	str x4, [x0, #1544]
	ldr x4, [x16, #48]
	str x4, [x0, #1552]
	ldr x4, [x16, #56]
	str x4, [x0, #1560]
	ldr x4, [x16, #64]
	str x4, [x0, #1568]
	ldr x4, [x16, #72]
	str x4, [x0, #1576]
	ldr x4, [x16, #80]
	str x4, [x0, #1584]
	ldr x4, [x16, #88]
	str x4, [x0, #1592]
	ldr x4, [x16, #96]
	str x4, [x0, #1600]
	ldr x4, [x16, #104]
	str x4, [x0, #1608]
	ldr x4, [x16, #112]
	str x4, [x0, #1616]
	ldr x4, [x16, #120]
	str x4, [x0, #1624]
	ldr x4, [x16, #128]
	str x4, [x0, #1632]
	ldr x4, [x16, #136]
	str x4, [x0, #1640]
	ldr x1, [x0, #424]
	str x1, [x0, #1648]
	ldr x1, [x0, #432]
	str x1, [x0, #1656]
	ldr x1, [x0, #440]
	str x1, [x0, #1664]
	ldr x1, [x0, #448]
	str x1, [x0, #1672]
	ldr x1, [x0, #456]
	str x1, [x0, #1680]
	ldr x1, [x0, #464]
	str x1, [x0, #1688]
	ldr x1, [x0, #472]
	str x1, [x0, #1696]
	ldr x1, [x0, #480]
	str x1, [x0, #1704]
	ldr x1, [x0, #488]
	str x1, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #3304]
	lsr x3, x3, #7
	cbnz x3, 250f
	b 251f
250:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
251:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1224]
	orr x1, x1, x2
	ldr x2, [x0, #1232]
	orr x1, x1, x2
	ldr x2, [x0, #1240]
	orr x1, x1, x2
	ldr x2, [x0, #1248]
	orr x1, x1, x2
	ldr x2, [x0, #1256]
	orr x1, x1, x2
	ldr x2, [x0, #1264]
	orr x1, x1, x2
	ldr x2, [x0, #1272]
	orr x1, x1, x2
	ldr x2, [x0, #1280]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 252f
	ldr x1, [x0, #1072]
	str x1, [x0, #1864]
	ldr x1, [x0, #1080]
	str x1, [x0, #1872]
	ldr x1, [x0, #1088]
	str x1, [x0, #1880]
	ldr x1, [x0, #1096]
	str x1, [x0, #1888]
	ldr x1, [x0, #1104]
	str x1, [x0, #1896]
	ldr x1, [x0, #1112]
	str x1, [x0, #1904]
	ldr x1, [x0, #1120]
	str x1, [x0, #1912]
	ldr x1, [x0, #1128]
	str x1, [x0, #1920]
	ldr x1, [x0, #1136]
	str x1, [x0, #1928]
	ldr x1, [x0, #1144]
	str x1, [x0, #2008]
	ldr x1, [x0, #1152]
	str x1, [x0, #2016]
	ldr x1, [x0, #1160]
	str x1, [x0, #2024]
	ldr x1, [x0, #1168]
	str x1, [x0, #2032]
	ldr x1, [x0, #1176]
	str x1, [x0, #2040]
	ldr x1, [x0, #1184]
	str x1, [x0, #2048]
	ldr x1, [x0, #1192]
	str x1, [x0, #2056]
	ldr x1, [x0, #1200]
	str x1, [x0, #2064]
	ldr x1, [x0, #1208]
	str x1, [x0, #2072]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 254f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	b 255f
254:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 256f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1376]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1488]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1496]
	b 257f
256:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1288, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1432]
	ldr x9, [x0, #1440]
	ldr x10, [x0, #1448]
	ldr x11, [x0, #1456]
	ldr x12, [x0, #1464]
	ldr x13, [x0, #1472]
	ldr x14, [x0, #1480]
	ldr x15, [x0, #1488]
	ldr x21, [x0, #1496]
	ldr x2, [x0, #1432]
	adds x8, x8, x2
	ldr x2, [x0, #1440]
	adcs x9, x9, x2
	ldr x2, [x0, #1448]
	adcs x10, x10, x2
	ldr x2, [x0, #1456]
	adcs x11, x11, x2
	ldr x2, [x0, #1464]
	adcs x12, x12, x2
	ldr x2, [x0, #1472]
	adcs x13, x13, x2
	ldr x2, [x0, #1480]
	adcs x14, x14, x2
	ldr x2, [x0, #1488]
	adcs x15, x15, x2
	ldr x2, [x0, #1496]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
257:
255:
	b 253f
252:
	ldr x1, [x0, #1504]
	str x1, [x0, #1288]
	ldr x1, [x0, #1512]
	str x1, [x0, #1296]
	ldr x1, [x0, #1520]
	str x1, [x0, #1304]
	ldr x1, [x0, #1528]
	str x1, [x0, #1312]
	ldr x1, [x0, #1536]
	str x1, [x0, #1320]
	ldr x1, [x0, #1544]
	str x1, [x0, #1328]
	ldr x1, [x0, #1552]
	str x1, [x0, #1336]
	ldr x1, [x0, #1560]
	str x1, [x0, #1344]
	ldr x1, [x0, #1568]
	str x1, [x0, #1352]
	ldr x1, [x0, #1576]
	str x1, [x0, #1360]
	ldr x1, [x0, #1584]
	str x1, [x0, #1368]
	ldr x1, [x0, #1592]
	str x1, [x0, #1376]
	ldr x1, [x0, #1600]
	str x1, [x0, #1384]
	ldr x1, [x0, #1608]
	str x1, [x0, #1392]
	ldr x1, [x0, #1616]
	str x1, [x0, #1400]
	ldr x1, [x0, #1624]
	str x1, [x0, #1408]
	ldr x1, [x0, #1632]
	str x1, [x0, #1416]
	ldr x1, [x0, #1640]
	str x1, [x0, #1424]
	ldr x1, [x0, #1648]
	str x1, [x0, #1432]
	ldr x1, [x0, #1656]
	str x1, [x0, #1440]
	ldr x1, [x0, #1664]
	str x1, [x0, #1448]
	ldr x1, [x0, #1672]
	str x1, [x0, #1456]
	ldr x1, [x0, #1680]
	str x1, [x0, #1464]
	ldr x1, [x0, #1688]
	str x1, [x0, #1472]
	ldr x1, [x0, #1696]
	str x1, [x0, #1480]
	ldr x1, [x0, #1704]
	str x1, [x0, #1488]
	ldr x1, [x0, #1712]
	str x1, [x0, #1496]
253:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
249:
	cbnz x19, 235b
	ldr x1, [x0, #1072]
	str x1, [x0, #1504]
	ldr x1, [x0, #1080]
	str x1, [x0, #1512]
	ldr x1, [x0, #1088]
	str x1, [x0, #1520]
	ldr x1, [x0, #1096]
	str x1, [x0, #1528]
	ldr x1, [x0, #1104]
	str x1, [x0, #1536]
	ldr x1, [x0, #1112]
	str x1, [x0, #1544]
	ldr x1, [x0, #1120]
	str x1, [x0, #1552]
	ldr x1, [x0, #1128]
	str x1, [x0, #1560]
	ldr x1, [x0, #1136]
	str x1, [x0, #1568]
	ldr x1, [x0, #1144]
	str x1, [x0, #1576]
	ldr x1, [x0, #1152]
	str x1, [x0, #1584]
	ldr x1, [x0, #1160]
	str x1, [x0, #1592]
	ldr x1, [x0, #1168]
	str x1, [x0, #1600]
	ldr x1, [x0, #1176]
	str x1, [x0, #1608]
	ldr x1, [x0, #1184]
	str x1, [x0, #1616]
	ldr x1, [x0, #1192]
	str x1, [x0, #1624]
	ldr x1, [x0, #1200]
	str x1, [x0, #1632]
	ldr x1, [x0, #1208]
	str x1, [x0, #1640]
	ldr x1, [x0, #1216]
	str x1, [x0, #1648]
	ldr x1, [x0, #1224]
	str x1, [x0, #1656]
	ldr x1, [x0, #1232]
	str x1, [x0, #1664]
	ldr x1, [x0, #1240]
	str x1, [x0, #1672]
	ldr x1, [x0, #1248]
	str x1, [x0, #1680]
	ldr x1, [x0, #1256]
	str x1, [x0, #1688]
	ldr x1, [x0, #1264]
	str x1, [x0, #1696]
	ldr x1, [x0, #1272]
	str x1, [x0, #1704]
	ldr x1, [x0, #1280]
	str x1, [x0, #1712]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1648, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1576]
	ldr x9, [x0, #1584]
	ldr x10, [x0, #1592]
	ldr x11, [x0, #1600]
	ldr x12, [x0, #1608]
	ldr x13, [x0, #1616]
	ldr x14, [x0, #1624]
	ldr x15, [x0, #1632]
	ldr x21, [x0, #1640]
	ldr x2, [x0, #280]
	adds x8, x8, x2
	ldr x2, [x0, #288]
	adcs x9, x9, x2
	ldr x2, [x0, #296]
	adcs x10, x10, x2
	ldr x2, [x0, #304]
	adcs x11, x11, x2
	ldr x2, [x0, #312]
	adcs x12, x12, x2
	ldr x2, [x0, #320]
	adcs x13, x13, x2
	ldr x2, [x0, #328]
	adcs x14, x14, x2
	ldr x2, [x0, #336]
	adcs x15, x15, x2
	ldr x2, [x0, #344]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1648]
	ldr x2, [x0, #1656]
	orr x1, x1, x2
	ldr x2, [x0, #1664]
	orr x1, x1, x2
	ldr x2, [x0, #1672]
	orr x1, x1, x2
	ldr x2, [x0, #1680]
	orr x1, x1, x2
	ldr x2, [x0, #1688]
	orr x1, x1, x2
	ldr x2, [x0, #1696]
	orr x1, x1, x2
	ldr x2, [x0, #1704]
	orr x1, x1, x2
	ldr x2, [x0, #1712]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x9, [x0, #1144]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #128, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1144]
	ldr x9, [x0, #1152]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1152]
	ldr x9, [x0, #1160]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1160]
	ldr x9, [x0, #1168]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1168]
	ldr x9, [x0, #1176]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1176]
	ldr x9, [x0, #1184]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1184]
	ldr x9, [x0, #1192]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1192]
	ldr x9, [x0, #1200]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1200]
	ldr x9, [x0, #1208]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2512]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #16384, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2520]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2528]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2536]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2552]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2560]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2568]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2576]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #1279, lsl #48
	str x1, [x0, #2152]
	movz x1, #39986, lsl #0
	movk x1, #36680, lsl #16
	movk x1, #47067, lsl #32
	movk x1, #55133, lsl #48
	str x1, [x0, #2160]
	movz x1, #52771, lsl #0
	movk x1, #56388, lsl #16
	movk x1, #56036, lsl #32
	movk x1, #59421, lsl #48
	str x1, [x0, #2168]
	movz x1, #34002, lsl #0
	movk x1, #42107, lsl #16
	movk x1, #58880, lsl #32
	movk x1, #13759, lsl #48
	str x1, [x0, #2176]
	movz x1, #38859, lsl #0
	movk x1, #49631, lsl #16
	movk x1, #49987, lsl #32
	movk x1, #64808, lsl #48
	str x1, [x0, #2184]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2192]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2200]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2208]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2216]
	movz x1, #39926, lsl #0
	movk x1, #28359, lsl #16
	movk x1, #18657, lsl #32
	movk x1, #17552, lsl #48
	str x1, [x0, #136]
	movz x1, #47185, lsl #0
	movk x1, #30307, lsl #16
	movk x1, #13895, lsl #32
	movk x1, #50250, lsl #48
	str x1, [x0, #144]
	movz x1, #23087, lsl #0
	movk x1, #2294, lsl #16
	movk x1, #65207, lsl #32
	movk x1, #32819, lsl #48
	str x1, [x0, #152]
	movz x1, #27028, lsl #0
	movk x1, #16592, lsl #16
	movk x1, #30844, lsl #32
	movk x1, #44665, lsl #48
	str x1, [x0, #160]
	movz x1, #5, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2512]
	ldr x5, [x0, #2520]
	ldr x16, [x0, #2528]
	ldr x17, [x0, #2536]
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x21, #0, lsl #0
	movz x22, #0, lsl #0
	movz x23, #0, lsl #0
	ldr x1, [x0, #2296]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	lsl x2, x8, #9
	adds x21, x21, x2
	lsr x2, x8, #55
	adcs x22, x22, x2
	adcs x23, x23, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #2304]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	lsl x2, x9, #9
	adds x22, x22, x2
	lsr x2, x9, #55
	adcs x23, x23, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #2312]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	lsl x2, x10, #9
	adds x23, x23, x2
	lsr x2, x10, #55
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #2320]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #9
	adds x8, x8, x2
	lsr x2, x11, #55
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	ldr x1, [x0, #2328]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	lsl x2, x12, #9
	adds x9, x9, x2
	lsr x2, x12, #55
	adcs x10, x10, x2
	adcs x11, x11, x7
	movz x12, #0, lsl #0
	ldr x1, [x0, #2336]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	lsl x2, x13, #9
	adds x10, x10, x2
	lsr x2, x13, #55
	adcs x11, x11, x2
	adcs x12, x12, x7
	movz x13, #0, lsl #0
	ldr x1, [x0, #2344]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	lsl x2, x14, #9
	adds x11, x11, x2
	lsr x2, x14, #55
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x14, #0, lsl #0
	ldr x1, [x0, #2352]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x23, x23, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x15, #9
	adds x12, x12, x2
	lsr x2, x15, #55
	adcs x13, x13, x2
	adcs x14, x14, x7
	movz x15, #0, lsl #0
	ldr x1, [x0, #2360]
	mul x2, x1, x4
	adds x21, x21, x2
	mul x2, x1, x5
	adcs x22, x22, x2
	mul x2, x1, x16
	adcs x23, x23, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #2544]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #2552]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2560]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #2568]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #2576]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #2576]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x22, x22, x2
	umulh x2, x1, x5
	adcs x23, x23, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #2544]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #2552]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #2560]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #2568]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	lsl x2, x21, #9
	adds x13, x13, x2
	lsr x2, x21, #55
	adcs x14, x14, x2
	adcs x15, x15, x7
	movz x21, #0, lsl #0
	ldr x2, [x0, #64]
	subs x1, x22, x2
	ldr x2, [x0, #72]
	sbcs x3, x23, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	ldr x2, [x0, #104]
	sbcs x16, x11, x2
	ldr x2, [x0, #112]
	sbcs x17, x12, x2
	ldr x2, [x0, #120]
	sbcs x24, x13, x2
	ldr x2, [x0, #128]
	sbcs x25, x14, x2
	sbcs x2, x15, x7
	csel x22, x1, x22, hs
	csel x23, x3, x23, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	csel x14, x25, x14, hs
	str x22, [x0, #2512]
	str x23, [x0, #2520]
	str x8, [x0, #2528]
	str x9, [x0, #2536]
	str x10, [x0, #2544]
	str x11, [x0, #2552]
	str x12, [x0, #2560]
	str x13, [x0, #2568]
	str x14, [x0, #2576]
	mov v29.d[0], x30
	movz x1, #2584, lsl #0
	movz x2, #2512, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #2584]
	subs x8, x8, x2
	ldr x2, [x0, #2592]
	sbcs x9, x9, x2
	ldr x2, [x0, #2600]
	sbcs x10, x10, x2
	ldr x2, [x0, #2608]
	sbcs x11, x11, x2
	ldr x2, [x0, #2616]
	sbcs x12, x12, x2
	ldr x2, [x0, #2624]
	sbcs x13, x13, x2
	ldr x2, [x0, #2632]
	sbcs x14, x14, x2
	ldr x2, [x0, #2640]
	sbcs x15, x15, x2
	ldr x2, [x0, #2648]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2944]
	str x9, [x0, #2952]
	str x10, [x0, #2960]
	str x11, [x0, #2968]
	str x12, [x0, #2976]
	str x13, [x0, #2984]
	str x14, [x0, #2992]
	str x15, [x0, #3000]
	str x21, [x0, #3008]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2512]
	ldr x9, [x0, #2520]
	ldr x10, [x0, #2528]
	ldr x11, [x0, #2536]
	ldr x12, [x0, #2544]
	ldr x13, [x0, #2552]
	ldr x14, [x0, #2560]
	ldr x15, [x0, #2568]
	ldr x21, [x0, #2576]
	ldr x2, [x0, #2152]
	adds x8, x8, x2
	ldr x2, [x0, #2160]
	adcs x9, x9, x2
	ldr x2, [x0, #2168]
	adcs x10, x10, x2
	ldr x2, [x0, #2176]
	adcs x11, x11, x2
	ldr x2, [x0, #2184]
	adcs x12, x12, x2
	ldr x2, [x0, #2192]
	adcs x13, x13, x2
	ldr x2, [x0, #2200]
	adcs x14, x14, x2
	ldr x2, [x0, #2208]
	adcs x15, x15, x2
	ldr x2, [x0, #2216]
	adcs x21, x21, x2
	adc x22, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #2512]
	str x9, [x0, #2520]
	str x10, [x0, #2528]
	str x11, [x0, #2536]
	str x12, [x0, #2544]
	str x13, [x0, #2552]
	str x14, [x0, #2560]
	str x15, [x0, #2568]
	str x21, [x0, #2576]
	mov v29.d[0], x30
	movz x1, #2584, lsl #0
	movz x2, #2512, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	ldr x2, [x0, #2584]
	subs x8, x8, x2
	ldr x2, [x0, #2592]
	sbcs x9, x9, x2
	ldr x2, [x0, #2600]
	sbcs x10, x10, x2
	ldr x2, [x0, #2608]
	sbcs x11, x11, x2
	ldr x2, [x0, #2616]
	sbcs x12, x12, x2
	ldr x2, [x0, #2624]
	sbcs x13, x13, x2
	ldr x2, [x0, #2632]
	sbcs x14, x14, x2
	ldr x2, [x0, #2640]
	sbcs x15, x15, x2
	ldr x2, [x0, #2648]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2800]
	str x9, [x0, #2808]
	str x10, [x0, #2816]
	str x11, [x0, #2824]
	str x12, [x0, #2832]
	str x13, [x0, #2840]
	str x14, [x0, #2848]
	str x15, [x0, #2856]
	str x21, [x0, #2864]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2944]
	ldr x2, [x0, #2952]
	orr x1, x1, x2
	ldr x2, [x0, #2960]
	orr x1, x1, x2
	ldr x2, [x0, #2968]
	orr x1, x1, x2
	ldr x2, [x0, #2976]
	orr x1, x1, x2
	ldr x2, [x0, #2984]
	orr x1, x1, x2
	ldr x2, [x0, #2992]
	orr x1, x1, x2
	ldr x2, [x0, #3000]
	orr x1, x1, x2
	ldr x2, [x0, #3008]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2296]
	ldr x2, [x0, #136]
	subs x16, x1, x2
	ldr x1, [x0, #2304]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2312]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2320]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2328]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2336]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2344]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	ldr x1, [x0, #2352]
	ldr x2, [x0, #192]
	sbcs x16, x1, x2
	ldr x1, [x0, #2360]
	ldr x2, [x0, #200]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x6, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2800]
	ldr x2, [x0, #2808]
	orr x1, x1, x2
	ldr x2, [x0, #2816]
	orr x1, x1, x2
	ldr x2, [x0, #2824]
	orr x1, x1, x2
	ldr x2, [x0, #2832]
	orr x1, x1, x2
	ldr x2, [x0, #2840]
	orr x1, x1, x2
	ldr x2, [x0, #2848]
	orr x1, x1, x2
	ldr x2, [x0, #2856]
	orr x1, x1, x2
	ldr x2, [x0, #2864]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	and x2, x2, x6
	orr x2, x2, x4
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1224]
	orr x1, x1, x2
	ldr x2, [x0, #1232]
	orr x1, x1, x2
	ldr x2, [x0, #1240]
	orr x1, x1, x2
	ldr x2, [x0, #1248]
	orr x1, x1, x2
	ldr x2, [x0, #1256]
	orr x1, x1, x2
	ldr x2, [x0, #1264]
	orr x1, x1, x2
	ldr x2, [x0, #1272]
	orr x1, x1, x2
	ldr x2, [x0, #1280]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	ldr x3, [x0, #3232]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ldr x25, [x0, #48]
	ldr x30, [x0, #56]
	movz x1, #1, lsl #0
	and x0, x3, x1
	add sp, sp, #80
	ret
	.p2align 6

vg_ecdsa_p521_sign:
	ldr x6, [x5, #32]
	ldr x7, [x5, #40]
	str x30, [sp, #-16]!
	sub sp, sp, #608
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x4, [x15, #184]
	str x6, [x15, #216]
	str x7, [x15, #224]
	str x5, [x15, #600]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	str x14, [x15, #368]
	str x14, [x15, #376]
	str x14, [x15, #384]
	ldr x13, [sp, #216]
	movz x9, #66, lsl #0
	subs x10, x13, x9
	csel x13, x9, x13, hs
	add x12, sp, #386
	sub x12, x12, x13
	ldr x11, [sp, #192]
20:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 20b
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #392]
	str x14, [x15, #400]
	str x14, [x15, #408]
	str x14, [x15, #416]
	str x14, [x15, #424]
	str x14, [x15, #432]
	str x14, [x15, #440]
	str x14, [x15, #448]
	str x14, [x15, #456]
	ldr x13, [sp, #216]
	add x12, sp, #457
	sub x12, x12, x13
	ldr x11, [sp, #192]
21:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 21b
	ldr x0, [sp, #184]
	add x6, sp, #392
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #1
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #1
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #1
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #1
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #1
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #1
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #1
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #1
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #1
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #0, lsl #0
	strb w11, [x9, #2256]
	add x12, x9, #2257
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #320
	add x14, x12, #66
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	ldr x11, [x13, #24]
	str x11, [x14, #24]
	ldr x11, [x13, #32]
	str x11, [x14, #32]
	ldr x11, [x13, #40]
	str x11, [x14, #40]
	ldr x11, [x13, #48]
	str x11, [x14, #48]
	ldr x11, [x13, #56]
	str x11, [x14, #56]
	add x13, x13, #58
	add x14, x14, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #133, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #133
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #0
	add x12, x9, #3072
	movz x13, #384, lsl #0
22:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 22b
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #1, lsl #0
	strb w11, [x9, #2256]
	add x12, x9, #2257
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x15, #320
	add x14, x12, #66
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	ldr x11, [x13, #24]
	str x11, [x14, #24]
	ldr x11, [x13, #32]
	str x11, [x14, #32]
	ldr x11, [x13, #40]
	str x11, [x14, #40]
	ldr x11, [x13, #48]
	str x11, [x14, #48]
	ldr x11, [x13, #56]
	str x11, [x14, #56]
	add x13, x13, #58
	add x14, x14, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x9, [sp, #184]
	add x11, x9, #3072
	add x12, x9, #0
	movz x13, #384, lsl #0
23:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 23b
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #133, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #133
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #0
	add x12, x9, #3072
	movz x13, #384, lsl #0
24:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 24b
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
25:
	movz x9, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #128]
26:
	ldr x9, [sp, #184]
	add x11, x9, #3072
	add x12, x9, #0
	movz x13, #384, lsl #0
27:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 27b
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	add x11, sp, #64
	add x12, sp, #464
	ldr x9, [sp, #128]
	add x12, x12, x9
	ldr x13, [sp, #216]
28:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 28b
	ldr x9, [sp, #128]
	ldr x10, [sp, #216]
	add x9, x9, x10
	add x15, sp, #0
	str x9, [x15, #128]
	movz x10, #66, lsl #0
	subs x12, x9, x10
	sbc x12, x12, x12
	cbnz x12, 26b
	ldr x0, [sp, #184]
	add x6, sp, #464
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #7
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #7
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #7
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #7
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #7
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #7
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #7
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #7
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #7
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	add x2, sp, #392
	add x3, sp, #464
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p521_sign_k}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 29f
	movz x12, #0, lsl #0
	b 210f
29:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #0, lsl #0
	strb w11, [x9, #2256]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #1, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #1
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #0
	add x12, x9, #3072
	movz x13, #384, lsl #0
211:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 211b
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	movz x12, #1, lsl #0
210:
	cbnz x12, 25b
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #232]
	str x14, [x15, #240]
	str x14, [x15, #248]
	str x14, [x15, #256]
	str x14, [x15, #264]
	str x14, [x15, #272]
	str x14, [x15, #280]
	str x14, [x15, #288]
	str x14, [x15, #296]
	str x14, [x15, #304]
	str x14, [x15, #312]
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	str x14, [x15, #368]
	str x14, [x15, #376]
	str x14, [x15, #384]
	str x14, [x15, #392]
	str x14, [x15, #400]
	str x14, [x15, #408]
	str x14, [x15, #416]
	str x14, [x15, #424]
	str x14, [x15, #432]
	str x14, [x15, #440]
	str x14, [x15, #448]
	str x14, [x15, #456]
	str x14, [x15, #464]
	str x14, [x15, #472]
	str x14, [x15, #480]
	str x14, [x15, #488]
	str x14, [x15, #496]
	str x14, [x15, #504]
	str x14, [x15, #512]
	str x14, [x15, #520]
	str x14, [x15, #528]
	str x14, [x15, #536]
	str x14, [x15, #544]
	str x14, [x15, #552]
	str x14, [x15, #560]
	str x14, [x15, #568]
	str x14, [x15, #576]
	str x14, [x15, #584]
	str x14, [x15, #592]
	add sp, sp, #608
	ldr x30, [sp], #16
	ret
	.p2align 6
