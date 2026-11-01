// The functions of `src/cmac_triple_des.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_triple_des_stream_init:
	sub sp, sp, #640
	add x3, sp, #0
	movz x9, #0, lsl #0
	str x9, [x0, #400]
	add x9, x0, #0
	add x0, x1, #0
	add x1, x2, #0
	add x2, x9, #0
	add x15, x3, #0
	ldr x5, [x0, #0]
	rev x5, x5
	str x5, [x15, #48]
	ldr x5, [x0, #8]
	rev x5, x5
	str x5, [x15, #56]
	sub x9, x1, #16
	cbz x9, 20f
	ldr x5, [x0, #16]
	b 21f
20:
	ldr x5, [x0, #0]
21:
	rev x5, x5
	str x5, [x15, #64]
	add x4, x15, #48
	movz x3, #3, lsl #0
22:
	ldr x5, [x4, #0]
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	ror x7, x5, #1
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #4
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #8, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16640, lsl #32
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1025, lsl #0
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #32
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #0]
	movz x11, #2048, lsl #0
	and x6, x5, x11
	movz x11, #256, lsl #0
	ror x7, x5, #1
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #8, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16640, lsl #32
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1025, lsl #0
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #8]
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	and x6, x5, x11
	movz x11, #128, lsl #0
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	movk x11, #1024, lsl #32
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #32
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #32
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #33, lsl #32
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #520, lsl #0
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #640, lsl #16
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	movk x11, #4096, lsl #32
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16640, lsl #32
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #16]
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	and x6, x5, x11
	movz x11, #8192, lsl #0
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16640, lsl #32
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #6144, lsl #0
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #640, lsl #16
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #24]
	movz x11, #2, lsl #0
	ror x6, x5, #1
	and x6, x6, x11
	movz x11, #32768, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #640, lsl #16
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	movk x11, #2048, lsl #32
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #48, lsl #0
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #6144, lsl #0
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #32]
	movz x11, #256, lsl #0
	ror x6, x5, #2
	and x6, x6, x11
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #4
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #640, lsl #16
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	movk x11, #16640, lsl #32
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #48, lsl #0
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #40]
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #160, lsl #0
	ror x7, x5, #4
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #20
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	movk x11, #16384, lsl #32
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #32
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #32
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	movk x11, #32768, lsl #32
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #513, lsl #16
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #48]
	movz x11, #16384, lsl #0
	ror x6, x5, #3
	and x6, x6, x11
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #16
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #160, lsl #0
	ror x7, x5, #20
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2, lsl #16
	movk x11, #16384, lsl #32
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #16
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #56]
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x6, x5, #3
	and x6, x6, x11
	movz x11, #2048, lsl #0
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #20
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #16
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	movk x11, #32768, lsl #32
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #160, lsl #0
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #16
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #64]
	movz x11, #1024, lsl #0
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #1
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #32
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #8192, lsl #16
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #260, lsl #32
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2048, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #2048, lsl #16
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16392, lsl #16
	movk x11, #2, lsl #32
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	movk x11, #32768, lsl #32
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #160, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #72]
	movz x11, #512, lsl #0
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #1
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #4
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #32
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #8192, lsl #16
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #144, lsl #0
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #16
	movk x11, #2, lsl #32
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #32
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #80]
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #32
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #32
	ror x7, x5, #8
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #20
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #24
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	movk x11, #1024, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #144, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #54
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #88]
	movz x11, #8, lsl #0
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #32
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #40, lsl #16
	movk x11, #32768, lsl #32
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	movk x11, #64, lsl #32
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1024, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #32
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1, lsl #0
	movk x11, #1, lsl #32
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #130, lsl #0
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #96]
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #32
	and x6, x5, x11
	movz x11, #1025, lsl #0
	ror x7, x5, #1
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #14
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	ror x7, x5, #21
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #22
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16640, lsl #0
	movk x11, #260, lsl #32
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	ror x7, x5, #31
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #32
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #35
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #40, lsl #16
	movk x11, #32769, lsl #32
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #32
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #50
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #58
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #104]
	movz x11, #512, lsl #0
	movk x11, #64, lsl #32
	ror x6, x5, #1
	and x6, x6, x11
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #2
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #5
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #7
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #12
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #16
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1025, lsl #0
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #19
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #26
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #29
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #32
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32784, lsl #16
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #32
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #39
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #43
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16640, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #44
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #48
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	movk x11, #2048, lsl #32
	ror x7, x5, #49
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #16
	movk x11, #32, lsl #32
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #59
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #62
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #112]
	movz x11, #2, lsl #0
	movk x11, #8, lsl #16
	movk x11, #32, lsl #32
	and x6, x5, x11
	movz x11, #0, lsl #0
	movk x11, #1024, lsl #16
	ror x7, x5, #3
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32, lsl #0
	ror x7, x5, #6
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #512, lsl #0
	movk x11, #64, lsl #32
	ror x7, x5, #9
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1, lsl #16
	ror x7, x5, #10
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #128, lsl #16
	ror x7, x5, #11
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #512, lsl #16
	ror x7, x5, #13
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4096, lsl #0
	movk x11, #128, lsl #32
	ror x7, x5, #15
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #32
	ror x7, x5, #17
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8, lsl #32
	ror x7, x5, #18
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8192, lsl #0
	ror x7, x5, #20
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16384, lsl #32
	ror x7, x5, #23
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #1025, lsl #0
	ror x7, x5, #25
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4096, lsl #16
	ror x7, x5, #27
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #32
	ror x7, x5, #28
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #64, lsl #0
	ror x7, x5, #30
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #24576, lsl #16
	ror x7, x5, #33
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #128, lsl #0
	movk x11, #4, lsl #16
	ror x7, x5, #34
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #32768, lsl #0
	ror x7, x5, #36
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #64, lsl #16
	ror x7, x5, #37
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16, lsl #0
	ror x7, x5, #38
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #8, lsl #0
	ror x7, x5, #40
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #8192, lsl #32
	ror x7, x5, #41
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #32
	ror x7, x5, #42
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32768, lsl #16
	ror x7, x5, #45
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	movk x11, #512, lsl #32
	ror x7, x5, #46
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #2048, lsl #0
	ror x7, x5, #47
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #4, lsl #32
	ror x7, x5, #51
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #256, lsl #0
	movk x11, #256, lsl #32
	ror x7, x5, #52
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #16384, lsl #0
	ror x7, x5, #53
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #4, lsl #0
	movk x11, #256, lsl #16
	ror x7, x5, #55
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2, lsl #16
	ror x7, x5, #56
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #2048, lsl #16
	ror x7, x5, #57
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32, lsl #16
	ror x7, x5, #60
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #1026, lsl #32
	ror x7, x5, #61
	and x7, x7, x11
	eor x6, x6, x7
	movz x11, #0, lsl #0
	movk x11, #32769, lsl #32
	ror x7, x5, #63
	and x7, x7, x11
	eor x6, x6, x7
	str x6, [x2, #120]
	add x2, x2, #128
	add x4, x4, #8
	sub x3, x3, #1
	cbnz x3, 22b
	sub x14, x2, #384
	movz x5, #0, lsl #0
	str x19, [x15, #384]
	str x20, [x15, #392]
	str x21, [x15, #400]
	str x22, [x15, #408]
	str x23, [x15, #416]
	str x24, [x15, #424]
	str x25, [x15, #432]
	str x26, [x15, #440]
	str x27, [x15, #448]
	movz x6, #5427, lsl #0
	movk x6, #4656, lsl #16
	movk x6, #36, lsl #32
	movk x6, #801, lsl #48
	movz x7, #7483, lsl #0
	movk x7, #6712, lsl #16
	movk x7, #2092, lsl #32
	movk x7, #2857, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz x6, #63, lsl #0
	dup v6.16b, w6
	movz x6, #0, lsl #0
	movk x6, #16576, lsl #16
	movk x6, #49216, lsl #32
	movk x6, #32896, lsl #48
	dup v7.2d, x6
	add x6, x14, #0
	add x7, x15, #0
	movz x16, #24, lsl #0
23:
	ldr q0, [x6, #0]
	ushr v1.2d, v0.2d, #2
	ushr v2.2d, v0.2d, #4
	ushr v3.2d, v0.2d, #6
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v5.16b
	and v4.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v7.16b
	str q4, [x7, #0]
	add x6, x6, #16
	add x7, x7, #16
	sub x16, x16, #1
	cbnz x16, 23b
	movz x6, #43207, lsl #0
	movk x6, #32516, lsl #16
	movk x6, #5620, lsl #32
	movk x6, #42138, lsl #48
	movz x7, #26379, lsl #0
	movk x7, #2423, lsl #16
	movk x7, #24315, lsl #32
	movk x7, #37480, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17201, lsl #0
	movk x6, #34281, lsl #16
	movk x6, #27789, lsl #32
	movk x6, #56174, lsl #48
	movz x7, #55478, lsl #0
	movk x7, #46680, lsl #16
	movk x7, #47874, lsl #32
	movk x7, #24725, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #30124, lsl #0
	movk x6, #50714, lsl #16
	movk x6, #59469, lsl #32
	movk x6, #480, lsl #48
	movz x7, #3796, lsl #0
	movk x7, #61615, lsl #16
	movk x7, #36899, lsl #32
	movk x7, #16209, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7415, lsl #0
	movk x6, #64356, lsl #16
	movk x6, #39762, lsl #32
	movk x6, #26525, lsl #48
	movz x7, #58169, lsl #0
	movk x7, #10435, lsl #16
	movk x7, #1950, lsl #32
	movk x7, #56362, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #27622, lsl #0
	movk x6, #64553, lsl #16
	movk x6, #49157, lsl #32
	movk x6, #43926, lsl #48
	movz x7, #42963, lsl #0
	movk x7, #21358, lsl #16
	movk x7, #7546, lsl #32
	movk x7, #38593, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #38188, lsl #0
	movk x6, #179, lsl #16
	movk x6, #31058, lsl #32
	movk x6, #20221, lsl #48
	movz x7, #53917, lsl #0
	movk x7, #15360, lsl #16
	movk x7, #12009, lsl #32
	movk x7, #57630, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #64513, lsl #0
	movk x6, #3270, lsl #16
	movk x6, #4018, lsl #32
	movk x6, #29054, lsl #48
	movz x7, #12878, lsl #0
	movk x7, #61337, lsl #16
	movk x7, #49397, lsl #32
	movk x7, #6952, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #26617, lsl #0
	movk x6, #56092, lsl #16
	movk x6, #41613, lsl #32
	movk x6, #40083, lsl #48
	movz x7, #18533, lsl #0
	movk x7, #41330, lsl #16
	movk x7, #38658, lsl #32
	movk x7, #29935, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #40684, lsl #0
	movk x6, #54031, lsl #16
	movk x6, #26298, lsl #32
	movk x6, #7413, lsl #48
	movz x7, #31105, lsl #0
	movk x7, #60984, lsl #16
	movk x7, #33110, lsl #32
	movk x7, #26018, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #22532, lsl #0
	movk x6, #11745, lsl #16
	movk x6, #57619, lsl #32
	movk x6, #55884, lsl #48
	movz x7, #1270, lsl #0
	movk x7, #45915, lsl #16
	movk x7, #15177, lsl #32
	movk x7, #34495, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #25763, lsl #0
	movk x6, #16376, lsl #16
	movk x6, #4311, lsl #32
	movk x6, #59457, lsl #48
	movz x7, #41754, lsl #0
	movk x7, #17830, lsl #16
	movk x7, #57324, lsl #32
	movk x7, #37407, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #38783, lsl #0
	movk x6, #55300, lsl #16
	movk x6, #3428, lsl #32
	movk x6, #30650, lsl #48
	movz x7, #23053, lsl #0
	movk x7, #11489, lsl #16
	movk x7, #41107, lsl #32
	movk x7, #60248, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #51534, lsl #0
	movk x6, #22193, lsl #16
	movk x6, #59172, lsl #32
	movk x6, #11690, lsl #48
	movz x7, #7355, lsl #0
	movk x7, #53590, lsl #16
	movk x7, #21460, lsl #32
	movk x7, #41673, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #44597, lsl #0
	movk x6, #25548, lsl #16
	movk x6, #7121, lsl #32
	movk x6, #56383, lsl #48
	movz x7, #8267, lsl #0
	movk x7, #49056, lsl #16
	movk x7, #50222, lsl #32
	movk x7, #14419, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14419, lsl #0
	movk x6, #57692, lsl #16
	movk x6, #40867, lsl #32
	movk x6, #53961, lsl #48
	movz x7, #972, lsl #0
	movk x7, #7207, lsl #16
	movk x7, #42047, lsl #32
	movk x7, #28600, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #55200, lsl #0
	movk x6, #4027, lsl #16
	movk x6, #17468, lsl #32
	movk x6, #43462, lsl #48
	movz x7, #63574, lsl #0
	movk x7, #25177, lsl #16
	movk x7, #13251, lsl #32
	movk x7, #56356, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #64, lsl #0
	dup v4.16b, w6
	movz x6, #128, lsl #0
	dup v5.16b, w6
	movz x6, #192, lsl #0
	dup v6.16b, w6
	movz x19, #0, lsl #0
	movk x19, #16, lsl #32
	movk x19, #32, lsl #48
	movz x20, #8208, lsl #0
	movk x20, #2064, lsl #16
	movk x20, #4096, lsl #32
	movk x20, #512, lsl #48
	movz x21, #1026, lsl #0
	movk x21, #288, lsl #32
	movk x21, #256, lsl #48
	movz x22, #2080, lsl #0
	movk x22, #1282, lsl #16
	movk x22, #2048, lsl #32
	movk x22, #8198, lsl #48
	movz x23, #0, lsl #0
	movk x23, #4, lsl #16
	movz x24, #0, lsl #0
	movk x24, #2048, lsl #48
	movz x25, #257, lsl #0
	movk x25, #512, lsl #16
	movk x25, #1032, lsl #32
	movk x25, #8, lsl #48
	movz x26, #0, lsl #0
	movk x26, #8201, lsl #16
	movk x26, #4096, lsl #48
	movz x27, #4608, lsl #0
	movk x27, #4096, lsl #16
	movk x27, #517, lsl #32
	movk x27, #1, lsl #48
	movz x0, #4, lsl #0
	movk x0, #32, lsl #16
	movk x0, #1024, lsl #48
	movz x8, #8, lsl #0
	movk x8, #8194, lsl #32
	movk x8, #16, lsl #48
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x11, x5, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #1
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #2
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #3
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #6
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #7
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #9
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #11
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #12
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #15
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #16
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4, lsl #0
	ror x6, x5, #18
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #20
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #512, lsl #0
	ror x6, x5, #21
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2, lsl #0
	ror x6, x5, #27
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #29
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #31
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #36
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #37
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #38
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #40
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #43
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #44
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #46
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #47
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #49
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #52
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #53
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #55
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #56
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #57
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #58
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #61
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #62
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	ror x12, x5, #1
	and x12, x12, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #2
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #3
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #4
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #7
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #8
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #11
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #12
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #13
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #16
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #17
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4, lsl #0
	ror x6, x5, #19
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #21
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #512, lsl #0
	ror x6, x5, #22
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2, lsl #0
	ror x6, x5, #28
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #31
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #32
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #37
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #38
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #39
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #41
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #44
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #45
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #47
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #48
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #50
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #53
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #54
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #56
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #57
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #58
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #59
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #62
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #63
	and x6, x6, x7
	eor x12, x12, x6
	add x10, x15, #0
	movz x16, #8, lsl #0
24:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 24b
	add x10, x10, #120
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
25:
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 25b
	add x10, x10, #136
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
26:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 26b
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x5, x12, x7
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	ror x6, x12, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #32
	ror x6, x12, #3
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #64, lsl #0
	movk x7, #16, lsl #48
	ror x6, x12, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #48
	ror x6, x12, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x12, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x12, #9
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #256, lsl #0
	ror x6, x12, #11
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x12, #15
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1024, lsl #0
	ror x6, x12, #17
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1, lsl #0
	ror x6, x12, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #48
	ror x6, x12, #21
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4, lsl #0
	ror x6, x12, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x12, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x12, #28
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x12, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #32
	ror x6, x12, #34
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x12, #37
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #16
	ror x6, x12, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #48
	ror x6, x12, #44
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x12, #46
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #32
	ror x6, x12, #48
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #16
	ror x6, x12, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #32
	ror x6, x12, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x12, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4096, lsl #0
	ror x6, x12, #55
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	ror x6, x12, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #48
	ror x6, x12, #58
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #16384, lsl #0
	ror x6, x12, #61
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x12, #63
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x11, #1
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x11, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #128, lsl #0
	movk x7, #32, lsl #48
	ror x6, x11, #5
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #48
	ror x6, x11, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x11, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x11, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #512, lsl #0
	ror x6, x11, #10
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x11, #14
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2048, lsl #0
	ror x6, x11, #16
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2, lsl #0
	ror x6, x11, #19
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #48
	ror x6, x11, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8, lsl #0
	ror x6, x11, #25
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x11, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #32
	ror x6, x11, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #48
	ror x6, x11, #32
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #32
	ror x6, x11, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	ror x6, x11, #36
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #16
	ror x6, x11, #42
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #48
	ror x6, x11, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	ror x6, x11, #45
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x11, #47
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #16
	ror x6, x11, #51
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #32
	ror x6, x11, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x11, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8192, lsl #0
	ror x6, x11, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x11, #56
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #48
	ror x6, x11, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32768, lsl #0
	ror x6, x11, #60
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x11, #62
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32, lsl #0
	movk x7, #8, lsl #48
	ror x6, x11, #63
	and x6, x6, x7
	eor x5, x5, x6
	ldr x19, [x15, #384]
	ldr x20, [x15, #392]
	ldr x21, [x15, #400]
	ldr x22, [x15, #408]
	ldr x23, [x15, #416]
	ldr x24, [x15, #424]
	ldr x25, [x15, #432]
	ldr x26, [x15, #440]
	ldr x27, [x15, #448]
	lsr x6, x5, #63
	movz x7, #0, lsl #0
	sub x7, x7, x6
	movz x11, #27, lsl #0
	and x7, x7, x11
	add x5, x5, x5
	eor x5, x5, x7
	rev x6, x5
	str x6, [x2, #0]
	lsr x6, x5, #63
	movz x7, #0, lsl #0
	sub x7, x7, x6
	movz x11, #27, lsl #0
	and x7, x7, x11
	add x5, x5, x5
	eor x5, x5, x7
	rev x6, x5
	str x6, [x2, #8]
	add sp, sp, #640
	ret
	.p2align 6

vg_cmac_triple_des_absorb:
	sub sp, sp, #688
	add x4, sp, #0
	str x19, [x4, #640]
	str x20, [x4, #648]
	str x21, [x4, #656]
	str x22, [x4, #664]
	str x23, [x4, #672]
	add x19, x0, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	cbz x1, 20f
	sub x9, x1, #1
	movz x10, #7, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	b 21f
20:
	movz x9, #0, lsl #0
21:
	lsr x10, x22, #3
	cbz x10, 22f
	movz x10, #8, lsl #0
	b 23f
22:
	add x10, x22, #0
23:
	movz x8, #8, lsl #0
	sub x8, x8, x9
	sub x11, x10, x8
	lsr x11, x11, #63
	cbz x11, 24f
	add x8, x10, #0
	b 25f
24:
25:
	add x10, x8, #0
	add x6, x19, x9
	add x6, x6, #408
	add x7, x21, #0
	cbz x8, 26f
28:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 28b
	b 27f
26:
27:
	add x21, x21, x10
	sub x22, x22, x10
	movz x3, #0, lsl #0
	cbz x22, 29f
	movz x3, #1, lsl #0
	b 210f
29:
210:
	add x0, x19, #0
	add x1, x19, #400
	add x2, x19, #408
	add x4, x23, #0
	add x14, x0, #0
	add x15, x4, #0
	cbz x3, 211f
	str x19, [x15, #384]
	str x20, [x15, #392]
	str x21, [x15, #400]
	str x22, [x15, #408]
	str x23, [x15, #416]
	str x24, [x15, #424]
	str x25, [x15, #432]
	str x26, [x15, #440]
	str x27, [x15, #448]
	movz x6, #5427, lsl #0
	movk x6, #4656, lsl #16
	movk x6, #36, lsl #32
	movk x6, #801, lsl #48
	movz x7, #7483, lsl #0
	movk x7, #6712, lsl #16
	movk x7, #2092, lsl #32
	movk x7, #2857, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz x6, #63, lsl #0
	dup v6.16b, w6
	movz x6, #0, lsl #0
	movk x6, #16576, lsl #16
	movk x6, #49216, lsl #32
	movk x6, #32896, lsl #48
	dup v7.2d, x6
	add x6, x14, #0
	add x7, x15, #0
	movz x16, #24, lsl #0
213:
	ldr q0, [x6, #0]
	ushr v1.2d, v0.2d, #2
	ushr v2.2d, v0.2d, #4
	ushr v3.2d, v0.2d, #6
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v5.16b
	and v4.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v7.16b
	str q4, [x7, #0]
	add x6, x6, #16
	add x7, x7, #16
	sub x16, x16, #1
	cbnz x16, 213b
	movz x6, #43207, lsl #0
	movk x6, #32516, lsl #16
	movk x6, #5620, lsl #32
	movk x6, #42138, lsl #48
	movz x7, #26379, lsl #0
	movk x7, #2423, lsl #16
	movk x7, #24315, lsl #32
	movk x7, #37480, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17201, lsl #0
	movk x6, #34281, lsl #16
	movk x6, #27789, lsl #32
	movk x6, #56174, lsl #48
	movz x7, #55478, lsl #0
	movk x7, #46680, lsl #16
	movk x7, #47874, lsl #32
	movk x7, #24725, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #30124, lsl #0
	movk x6, #50714, lsl #16
	movk x6, #59469, lsl #32
	movk x6, #480, lsl #48
	movz x7, #3796, lsl #0
	movk x7, #61615, lsl #16
	movk x7, #36899, lsl #32
	movk x7, #16209, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7415, lsl #0
	movk x6, #64356, lsl #16
	movk x6, #39762, lsl #32
	movk x6, #26525, lsl #48
	movz x7, #58169, lsl #0
	movk x7, #10435, lsl #16
	movk x7, #1950, lsl #32
	movk x7, #56362, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #27622, lsl #0
	movk x6, #64553, lsl #16
	movk x6, #49157, lsl #32
	movk x6, #43926, lsl #48
	movz x7, #42963, lsl #0
	movk x7, #21358, lsl #16
	movk x7, #7546, lsl #32
	movk x7, #38593, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #38188, lsl #0
	movk x6, #179, lsl #16
	movk x6, #31058, lsl #32
	movk x6, #20221, lsl #48
	movz x7, #53917, lsl #0
	movk x7, #15360, lsl #16
	movk x7, #12009, lsl #32
	movk x7, #57630, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #64513, lsl #0
	movk x6, #3270, lsl #16
	movk x6, #4018, lsl #32
	movk x6, #29054, lsl #48
	movz x7, #12878, lsl #0
	movk x7, #61337, lsl #16
	movk x7, #49397, lsl #32
	movk x7, #6952, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #26617, lsl #0
	movk x6, #56092, lsl #16
	movk x6, #41613, lsl #32
	movk x6, #40083, lsl #48
	movz x7, #18533, lsl #0
	movk x7, #41330, lsl #16
	movk x7, #38658, lsl #32
	movk x7, #29935, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #40684, lsl #0
	movk x6, #54031, lsl #16
	movk x6, #26298, lsl #32
	movk x6, #7413, lsl #48
	movz x7, #31105, lsl #0
	movk x7, #60984, lsl #16
	movk x7, #33110, lsl #32
	movk x7, #26018, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #22532, lsl #0
	movk x6, #11745, lsl #16
	movk x6, #57619, lsl #32
	movk x6, #55884, lsl #48
	movz x7, #1270, lsl #0
	movk x7, #45915, lsl #16
	movk x7, #15177, lsl #32
	movk x7, #34495, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #25763, lsl #0
	movk x6, #16376, lsl #16
	movk x6, #4311, lsl #32
	movk x6, #59457, lsl #48
	movz x7, #41754, lsl #0
	movk x7, #17830, lsl #16
	movk x7, #57324, lsl #32
	movk x7, #37407, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #38783, lsl #0
	movk x6, #55300, lsl #16
	movk x6, #3428, lsl #32
	movk x6, #30650, lsl #48
	movz x7, #23053, lsl #0
	movk x7, #11489, lsl #16
	movk x7, #41107, lsl #32
	movk x7, #60248, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #51534, lsl #0
	movk x6, #22193, lsl #16
	movk x6, #59172, lsl #32
	movk x6, #11690, lsl #48
	movz x7, #7355, lsl #0
	movk x7, #53590, lsl #16
	movk x7, #21460, lsl #32
	movk x7, #41673, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #44597, lsl #0
	movk x6, #25548, lsl #16
	movk x6, #7121, lsl #32
	movk x6, #56383, lsl #48
	movz x7, #8267, lsl #0
	movk x7, #49056, lsl #16
	movk x7, #50222, lsl #32
	movk x7, #14419, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14419, lsl #0
	movk x6, #57692, lsl #16
	movk x6, #40867, lsl #32
	movk x6, #53961, lsl #48
	movz x7, #972, lsl #0
	movk x7, #7207, lsl #16
	movk x7, #42047, lsl #32
	movk x7, #28600, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #55200, lsl #0
	movk x6, #4027, lsl #16
	movk x6, #17468, lsl #32
	movk x6, #43462, lsl #48
	movz x7, #63574, lsl #0
	movk x7, #25177, lsl #16
	movk x7, #13251, lsl #32
	movk x7, #56356, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #64, lsl #0
	dup v4.16b, w6
	movz x6, #128, lsl #0
	dup v5.16b, w6
	movz x6, #192, lsl #0
	dup v6.16b, w6
	movz x19, #0, lsl #0
	movk x19, #16, lsl #32
	movk x19, #32, lsl #48
	movz x20, #8208, lsl #0
	movk x20, #2064, lsl #16
	movk x20, #4096, lsl #32
	movk x20, #512, lsl #48
	movz x21, #1026, lsl #0
	movk x21, #288, lsl #32
	movk x21, #256, lsl #48
	movz x22, #2080, lsl #0
	movk x22, #1282, lsl #16
	movk x22, #2048, lsl #32
	movk x22, #8198, lsl #48
	movz x23, #0, lsl #0
	movk x23, #4, lsl #16
	movz x24, #0, lsl #0
	movk x24, #2048, lsl #48
	movz x25, #257, lsl #0
	movk x25, #512, lsl #16
	movk x25, #1032, lsl #32
	movk x25, #8, lsl #48
	movz x26, #0, lsl #0
	movk x26, #8201, lsl #16
	movk x26, #4096, lsl #48
	movz x27, #4608, lsl #0
	movk x27, #4096, lsl #16
	movk x27, #517, lsl #32
	movk x27, #1, lsl #48
	movz x0, #4, lsl #0
	movk x0, #32, lsl #16
	movk x0, #1024, lsl #48
	movz x8, #8, lsl #0
	movk x8, #8194, lsl #32
	movk x8, #16, lsl #48
214:
	ldr x5, [x1, #0]
	ldr x6, [x2, #0]
	eor x5, x5, x6
	rev x5, x5
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x11, x5, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #1
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #2
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #3
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #6
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #7
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #9
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #11
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #12
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #15
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #16
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4, lsl #0
	ror x6, x5, #18
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #20
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #512, lsl #0
	ror x6, x5, #21
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2, lsl #0
	ror x6, x5, #27
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #29
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #31
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #36
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #37
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #38
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #40
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #43
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #44
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #46
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #47
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #49
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #52
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #53
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #55
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #56
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #57
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #58
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #61
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #62
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	ror x12, x5, #1
	and x12, x12, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #2
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #3
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #4
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #7
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #8
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #11
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #12
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #13
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #16
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #17
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4, lsl #0
	ror x6, x5, #19
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #21
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #512, lsl #0
	ror x6, x5, #22
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2, lsl #0
	ror x6, x5, #28
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #31
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #32
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #37
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #38
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #39
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #41
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #44
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #45
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #47
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #48
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #50
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #53
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #54
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #56
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #57
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #58
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #59
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #62
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #63
	and x6, x6, x7
	eor x12, x12, x6
	add x10, x15, #0
	movz x16, #8, lsl #0
215:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 215b
	add x10, x10, #120
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
216:
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 216b
	add x10, x10, #136
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
217:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 217b
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x5, x12, x7
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	ror x6, x12, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #32
	ror x6, x12, #3
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #64, lsl #0
	movk x7, #16, lsl #48
	ror x6, x12, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #48
	ror x6, x12, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x12, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x12, #9
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #256, lsl #0
	ror x6, x12, #11
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x12, #15
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1024, lsl #0
	ror x6, x12, #17
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1, lsl #0
	ror x6, x12, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #48
	ror x6, x12, #21
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4, lsl #0
	ror x6, x12, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x12, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x12, #28
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x12, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #32
	ror x6, x12, #34
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x12, #37
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #16
	ror x6, x12, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #48
	ror x6, x12, #44
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x12, #46
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #32
	ror x6, x12, #48
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #16
	ror x6, x12, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #32
	ror x6, x12, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x12, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4096, lsl #0
	ror x6, x12, #55
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	ror x6, x12, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #48
	ror x6, x12, #58
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #16384, lsl #0
	ror x6, x12, #61
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x12, #63
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x11, #1
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x11, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #128, lsl #0
	movk x7, #32, lsl #48
	ror x6, x11, #5
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #48
	ror x6, x11, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x11, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x11, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #512, lsl #0
	ror x6, x11, #10
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x11, #14
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2048, lsl #0
	ror x6, x11, #16
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2, lsl #0
	ror x6, x11, #19
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #48
	ror x6, x11, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8, lsl #0
	ror x6, x11, #25
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x11, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #32
	ror x6, x11, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #48
	ror x6, x11, #32
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #32
	ror x6, x11, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	ror x6, x11, #36
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #16
	ror x6, x11, #42
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #48
	ror x6, x11, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	ror x6, x11, #45
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x11, #47
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #16
	ror x6, x11, #51
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #32
	ror x6, x11, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x11, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8192, lsl #0
	ror x6, x11, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x11, #56
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #48
	ror x6, x11, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32768, lsl #0
	ror x6, x11, #60
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x11, #62
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32, lsl #0
	movk x7, #8, lsl #48
	ror x6, x11, #63
	and x6, x6, x7
	eor x5, x5, x6
	rev x5, x5
	str x5, [x1, #0]
	add x2, x2, #8
	sub x3, x3, #1
	cbnz x3, 214b
	ldr x19, [x15, #384]
	ldr x20, [x15, #392]
	ldr x21, [x15, #400]
	ldr x22, [x15, #408]
	ldr x23, [x15, #416]
	ldr x24, [x15, #424]
	ldr x25, [x15, #432]
	ldr x26, [x15, #440]
	ldr x27, [x15, #448]
	b 212f
211:
212:
	movz x20, #0, lsl #0
	cbz x22, 218f
	sub x20, x22, #1
	movz x9, #7, lsl #0
	and x9, x20, x9
	sub x20, x20, x9
	b 219f
218:
219:
	lsr x3, x20, #3
	add x0, x19, #0
	add x1, x19, #400
	add x2, x21, #0
	add x4, x23, #0
	add x14, x0, #0
	add x15, x4, #0
	cbz x3, 220f
	str x19, [x15, #384]
	str x20, [x15, #392]
	str x21, [x15, #400]
	str x22, [x15, #408]
	str x23, [x15, #416]
	str x24, [x15, #424]
	str x25, [x15, #432]
	str x26, [x15, #440]
	str x27, [x15, #448]
	movz x6, #5427, lsl #0
	movk x6, #4656, lsl #16
	movk x6, #36, lsl #32
	movk x6, #801, lsl #48
	movz x7, #7483, lsl #0
	movk x7, #6712, lsl #16
	movk x7, #2092, lsl #32
	movk x7, #2857, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz x6, #63, lsl #0
	dup v6.16b, w6
	movz x6, #0, lsl #0
	movk x6, #16576, lsl #16
	movk x6, #49216, lsl #32
	movk x6, #32896, lsl #48
	dup v7.2d, x6
	add x6, x14, #0
	add x7, x15, #0
	movz x16, #24, lsl #0
222:
	ldr q0, [x6, #0]
	ushr v1.2d, v0.2d, #2
	ushr v2.2d, v0.2d, #4
	ushr v3.2d, v0.2d, #6
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v5.16b
	and v4.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v7.16b
	str q4, [x7, #0]
	add x6, x6, #16
	add x7, x7, #16
	sub x16, x16, #1
	cbnz x16, 222b
	movz x6, #43207, lsl #0
	movk x6, #32516, lsl #16
	movk x6, #5620, lsl #32
	movk x6, #42138, lsl #48
	movz x7, #26379, lsl #0
	movk x7, #2423, lsl #16
	movk x7, #24315, lsl #32
	movk x7, #37480, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17201, lsl #0
	movk x6, #34281, lsl #16
	movk x6, #27789, lsl #32
	movk x6, #56174, lsl #48
	movz x7, #55478, lsl #0
	movk x7, #46680, lsl #16
	movk x7, #47874, lsl #32
	movk x7, #24725, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #30124, lsl #0
	movk x6, #50714, lsl #16
	movk x6, #59469, lsl #32
	movk x6, #480, lsl #48
	movz x7, #3796, lsl #0
	movk x7, #61615, lsl #16
	movk x7, #36899, lsl #32
	movk x7, #16209, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7415, lsl #0
	movk x6, #64356, lsl #16
	movk x6, #39762, lsl #32
	movk x6, #26525, lsl #48
	movz x7, #58169, lsl #0
	movk x7, #10435, lsl #16
	movk x7, #1950, lsl #32
	movk x7, #56362, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #27622, lsl #0
	movk x6, #64553, lsl #16
	movk x6, #49157, lsl #32
	movk x6, #43926, lsl #48
	movz x7, #42963, lsl #0
	movk x7, #21358, lsl #16
	movk x7, #7546, lsl #32
	movk x7, #38593, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #38188, lsl #0
	movk x6, #179, lsl #16
	movk x6, #31058, lsl #32
	movk x6, #20221, lsl #48
	movz x7, #53917, lsl #0
	movk x7, #15360, lsl #16
	movk x7, #12009, lsl #32
	movk x7, #57630, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #64513, lsl #0
	movk x6, #3270, lsl #16
	movk x6, #4018, lsl #32
	movk x6, #29054, lsl #48
	movz x7, #12878, lsl #0
	movk x7, #61337, lsl #16
	movk x7, #49397, lsl #32
	movk x7, #6952, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #26617, lsl #0
	movk x6, #56092, lsl #16
	movk x6, #41613, lsl #32
	movk x6, #40083, lsl #48
	movz x7, #18533, lsl #0
	movk x7, #41330, lsl #16
	movk x7, #38658, lsl #32
	movk x7, #29935, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #40684, lsl #0
	movk x6, #54031, lsl #16
	movk x6, #26298, lsl #32
	movk x6, #7413, lsl #48
	movz x7, #31105, lsl #0
	movk x7, #60984, lsl #16
	movk x7, #33110, lsl #32
	movk x7, #26018, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #22532, lsl #0
	movk x6, #11745, lsl #16
	movk x6, #57619, lsl #32
	movk x6, #55884, lsl #48
	movz x7, #1270, lsl #0
	movk x7, #45915, lsl #16
	movk x7, #15177, lsl #32
	movk x7, #34495, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #25763, lsl #0
	movk x6, #16376, lsl #16
	movk x6, #4311, lsl #32
	movk x6, #59457, lsl #48
	movz x7, #41754, lsl #0
	movk x7, #17830, lsl #16
	movk x7, #57324, lsl #32
	movk x7, #37407, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #38783, lsl #0
	movk x6, #55300, lsl #16
	movk x6, #3428, lsl #32
	movk x6, #30650, lsl #48
	movz x7, #23053, lsl #0
	movk x7, #11489, lsl #16
	movk x7, #41107, lsl #32
	movk x7, #60248, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #51534, lsl #0
	movk x6, #22193, lsl #16
	movk x6, #59172, lsl #32
	movk x6, #11690, lsl #48
	movz x7, #7355, lsl #0
	movk x7, #53590, lsl #16
	movk x7, #21460, lsl #32
	movk x7, #41673, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #44597, lsl #0
	movk x6, #25548, lsl #16
	movk x6, #7121, lsl #32
	movk x6, #56383, lsl #48
	movz x7, #8267, lsl #0
	movk x7, #49056, lsl #16
	movk x7, #50222, lsl #32
	movk x7, #14419, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14419, lsl #0
	movk x6, #57692, lsl #16
	movk x6, #40867, lsl #32
	movk x6, #53961, lsl #48
	movz x7, #972, lsl #0
	movk x7, #7207, lsl #16
	movk x7, #42047, lsl #32
	movk x7, #28600, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #55200, lsl #0
	movk x6, #4027, lsl #16
	movk x6, #17468, lsl #32
	movk x6, #43462, lsl #48
	movz x7, #63574, lsl #0
	movk x7, #25177, lsl #16
	movk x7, #13251, lsl #32
	movk x7, #56356, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #64, lsl #0
	dup v4.16b, w6
	movz x6, #128, lsl #0
	dup v5.16b, w6
	movz x6, #192, lsl #0
	dup v6.16b, w6
	movz x19, #0, lsl #0
	movk x19, #16, lsl #32
	movk x19, #32, lsl #48
	movz x20, #8208, lsl #0
	movk x20, #2064, lsl #16
	movk x20, #4096, lsl #32
	movk x20, #512, lsl #48
	movz x21, #1026, lsl #0
	movk x21, #288, lsl #32
	movk x21, #256, lsl #48
	movz x22, #2080, lsl #0
	movk x22, #1282, lsl #16
	movk x22, #2048, lsl #32
	movk x22, #8198, lsl #48
	movz x23, #0, lsl #0
	movk x23, #4, lsl #16
	movz x24, #0, lsl #0
	movk x24, #2048, lsl #48
	movz x25, #257, lsl #0
	movk x25, #512, lsl #16
	movk x25, #1032, lsl #32
	movk x25, #8, lsl #48
	movz x26, #0, lsl #0
	movk x26, #8201, lsl #16
	movk x26, #4096, lsl #48
	movz x27, #4608, lsl #0
	movk x27, #4096, lsl #16
	movk x27, #517, lsl #32
	movk x27, #1, lsl #48
	movz x0, #4, lsl #0
	movk x0, #32, lsl #16
	movk x0, #1024, lsl #48
	movz x8, #8, lsl #0
	movk x8, #8194, lsl #32
	movk x8, #16, lsl #48
223:
	ldr x5, [x1, #0]
	ldr x6, [x2, #0]
	eor x5, x5, x6
	rev x5, x5
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x11, x5, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #1
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #2
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #3
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #6
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #7
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #9
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #11
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #12
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #15
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #16
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4, lsl #0
	ror x6, x5, #18
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #20
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #512, lsl #0
	ror x6, x5, #21
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2, lsl #0
	ror x6, x5, #27
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #29
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #31
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #36
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #37
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #38
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #40
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #43
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #44
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #46
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #47
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #49
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #52
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #53
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #55
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #56
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #57
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #58
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #61
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #62
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	ror x12, x5, #1
	and x12, x12, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #2
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #3
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #4
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #7
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #8
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #11
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #12
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #13
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #16
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #17
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4, lsl #0
	ror x6, x5, #19
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #21
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #512, lsl #0
	ror x6, x5, #22
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2, lsl #0
	ror x6, x5, #28
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #31
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #32
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #37
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #38
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #39
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #41
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #44
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #45
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #47
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #48
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #50
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #53
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #54
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #56
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #57
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #58
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #59
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #62
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #63
	and x6, x6, x7
	eor x12, x12, x6
	add x10, x15, #0
	movz x16, #8, lsl #0
224:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 224b
	add x10, x10, #120
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
225:
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 225b
	add x10, x10, #136
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
226:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 226b
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x5, x12, x7
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	ror x6, x12, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #32
	ror x6, x12, #3
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #64, lsl #0
	movk x7, #16, lsl #48
	ror x6, x12, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #48
	ror x6, x12, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x12, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x12, #9
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #256, lsl #0
	ror x6, x12, #11
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x12, #15
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1024, lsl #0
	ror x6, x12, #17
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1, lsl #0
	ror x6, x12, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #48
	ror x6, x12, #21
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4, lsl #0
	ror x6, x12, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x12, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x12, #28
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x12, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #32
	ror x6, x12, #34
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x12, #37
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #16
	ror x6, x12, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #48
	ror x6, x12, #44
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x12, #46
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #32
	ror x6, x12, #48
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #16
	ror x6, x12, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #32
	ror x6, x12, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x12, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4096, lsl #0
	ror x6, x12, #55
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	ror x6, x12, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #48
	ror x6, x12, #58
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #16384, lsl #0
	ror x6, x12, #61
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x12, #63
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x11, #1
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x11, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #128, lsl #0
	movk x7, #32, lsl #48
	ror x6, x11, #5
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #48
	ror x6, x11, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x11, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x11, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #512, lsl #0
	ror x6, x11, #10
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x11, #14
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2048, lsl #0
	ror x6, x11, #16
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2, lsl #0
	ror x6, x11, #19
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #48
	ror x6, x11, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8, lsl #0
	ror x6, x11, #25
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x11, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #32
	ror x6, x11, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #48
	ror x6, x11, #32
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #32
	ror x6, x11, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	ror x6, x11, #36
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #16
	ror x6, x11, #42
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #48
	ror x6, x11, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	ror x6, x11, #45
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x11, #47
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #16
	ror x6, x11, #51
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #32
	ror x6, x11, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x11, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8192, lsl #0
	ror x6, x11, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x11, #56
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #48
	ror x6, x11, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32768, lsl #0
	ror x6, x11, #60
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x11, #62
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32, lsl #0
	movk x7, #8, lsl #48
	ror x6, x11, #63
	and x6, x6, x7
	eor x5, x5, x6
	rev x5, x5
	str x5, [x1, #0]
	add x2, x2, #8
	sub x3, x3, #1
	cbnz x3, 223b
	ldr x19, [x15, #384]
	ldr x20, [x15, #392]
	ldr x21, [x15, #400]
	ldr x22, [x15, #408]
	ldr x23, [x15, #416]
	ldr x24, [x15, #424]
	ldr x25, [x15, #432]
	ldr x26, [x15, #440]
	ldr x27, [x15, #448]
	b 221f
220:
221:
	add x21, x21, x20
	sub x22, x22, x20
	add x6, x19, #408
	add x7, x21, #0
	add x8, x22, #0
	cbz x8, 227f
229:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 229b
	b 228f
227:
228:
	ldr x19, [x23, #640]
	ldr x20, [x23, #648]
	ldr x21, [x23, #656]
	ldr x22, [x23, #664]
	ldr x23, [x23, #672]
	add sp, sp, #688
	ret
	.p2align 6

vg_cmac_triple_des_finish:
	sub sp, sp, #640
	add x3, sp, #0
	ldr x9, [x0, #400]
	str x9, [x2, #0]
	add x4, x3, #0
	add x3, x1, #0
	add x1, x2, #0
	add x2, x0, #408
	cbz x3, 20f
	sub x3, x3, #1
	movz x9, #7, lsl #0
	and x3, x3, x9
	add x3, x3, #1
	b 21f
20:
21:
	add x14, x0, #0
	add x15, x4, #0
	sub x9, x3, #8
	cbz x9, 22f
	movz x5, #0, lsl #0
	str x5, [x15, #48]
	add x6, x15, #48
	add x7, x2, #0
	add x8, x3, #0
	cbz x3, 24f
26:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 26b
	b 25f
24:
25:
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x5, [x15, #48]
	ldr x6, [x0, #392]
	eor x5, x5, x6
	b 23f
22:
	ldr x5, [x2, #0]
	ldr x6, [x0, #384]
	eor x5, x5, x6
23:
	ldr x6, [x1, #0]
	eor x5, x5, x6
	rev x5, x5
	str x19, [x15, #384]
	str x20, [x15, #392]
	str x21, [x15, #400]
	str x22, [x15, #408]
	str x23, [x15, #416]
	str x24, [x15, #424]
	str x25, [x15, #432]
	str x26, [x15, #440]
	str x27, [x15, #448]
	movz x6, #5427, lsl #0
	movk x6, #4656, lsl #16
	movk x6, #36, lsl #32
	movk x6, #801, lsl #48
	movz x7, #7483, lsl #0
	movk x7, #6712, lsl #16
	movk x7, #2092, lsl #32
	movk x7, #2857, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz x6, #63, lsl #0
	dup v6.16b, w6
	movz x6, #0, lsl #0
	movk x6, #16576, lsl #16
	movk x6, #49216, lsl #32
	movk x6, #32896, lsl #48
	dup v7.2d, x6
	add x6, x14, #0
	add x7, x15, #0
	movz x16, #24, lsl #0
27:
	ldr q0, [x6, #0]
	ushr v1.2d, v0.2d, #2
	ushr v2.2d, v0.2d, #4
	ushr v3.2d, v0.2d, #6
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v5.16b
	and v4.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v7.16b
	str q4, [x7, #0]
	add x6, x6, #16
	add x7, x7, #16
	sub x16, x16, #1
	cbnz x16, 27b
	movz x6, #43207, lsl #0
	movk x6, #32516, lsl #16
	movk x6, #5620, lsl #32
	movk x6, #42138, lsl #48
	movz x7, #26379, lsl #0
	movk x7, #2423, lsl #16
	movk x7, #24315, lsl #32
	movk x7, #37480, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17201, lsl #0
	movk x6, #34281, lsl #16
	movk x6, #27789, lsl #32
	movk x6, #56174, lsl #48
	movz x7, #55478, lsl #0
	movk x7, #46680, lsl #16
	movk x7, #47874, lsl #32
	movk x7, #24725, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #30124, lsl #0
	movk x6, #50714, lsl #16
	movk x6, #59469, lsl #32
	movk x6, #480, lsl #48
	movz x7, #3796, lsl #0
	movk x7, #61615, lsl #16
	movk x7, #36899, lsl #32
	movk x7, #16209, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7415, lsl #0
	movk x6, #64356, lsl #16
	movk x6, #39762, lsl #32
	movk x6, #26525, lsl #48
	movz x7, #58169, lsl #0
	movk x7, #10435, lsl #16
	movk x7, #1950, lsl #32
	movk x7, #56362, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #27622, lsl #0
	movk x6, #64553, lsl #16
	movk x6, #49157, lsl #32
	movk x6, #43926, lsl #48
	movz x7, #42963, lsl #0
	movk x7, #21358, lsl #16
	movk x7, #7546, lsl #32
	movk x7, #38593, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #38188, lsl #0
	movk x6, #179, lsl #16
	movk x6, #31058, lsl #32
	movk x6, #20221, lsl #48
	movz x7, #53917, lsl #0
	movk x7, #15360, lsl #16
	movk x7, #12009, lsl #32
	movk x7, #57630, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #64513, lsl #0
	movk x6, #3270, lsl #16
	movk x6, #4018, lsl #32
	movk x6, #29054, lsl #48
	movz x7, #12878, lsl #0
	movk x7, #61337, lsl #16
	movk x7, #49397, lsl #32
	movk x7, #6952, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #26617, lsl #0
	movk x6, #56092, lsl #16
	movk x6, #41613, lsl #32
	movk x6, #40083, lsl #48
	movz x7, #18533, lsl #0
	movk x7, #41330, lsl #16
	movk x7, #38658, lsl #32
	movk x7, #29935, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #40684, lsl #0
	movk x6, #54031, lsl #16
	movk x6, #26298, lsl #32
	movk x6, #7413, lsl #48
	movz x7, #31105, lsl #0
	movk x7, #60984, lsl #16
	movk x7, #33110, lsl #32
	movk x7, #26018, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #22532, lsl #0
	movk x6, #11745, lsl #16
	movk x6, #57619, lsl #32
	movk x6, #55884, lsl #48
	movz x7, #1270, lsl #0
	movk x7, #45915, lsl #16
	movk x7, #15177, lsl #32
	movk x7, #34495, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #25763, lsl #0
	movk x6, #16376, lsl #16
	movk x6, #4311, lsl #32
	movk x6, #59457, lsl #48
	movz x7, #41754, lsl #0
	movk x7, #17830, lsl #16
	movk x7, #57324, lsl #32
	movk x7, #37407, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #38783, lsl #0
	movk x6, #55300, lsl #16
	movk x6, #3428, lsl #32
	movk x6, #30650, lsl #48
	movz x7, #23053, lsl #0
	movk x7, #11489, lsl #16
	movk x7, #41107, lsl #32
	movk x7, #60248, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #51534, lsl #0
	movk x6, #22193, lsl #16
	movk x6, #59172, lsl #32
	movk x6, #11690, lsl #48
	movz x7, #7355, lsl #0
	movk x7, #53590, lsl #16
	movk x7, #21460, lsl #32
	movk x7, #41673, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #44597, lsl #0
	movk x6, #25548, lsl #16
	movk x6, #7121, lsl #32
	movk x6, #56383, lsl #48
	movz x7, #8267, lsl #0
	movk x7, #49056, lsl #16
	movk x7, #50222, lsl #32
	movk x7, #14419, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14419, lsl #0
	movk x6, #57692, lsl #16
	movk x6, #40867, lsl #32
	movk x6, #53961, lsl #48
	movz x7, #972, lsl #0
	movk x7, #7207, lsl #16
	movk x7, #42047, lsl #32
	movk x7, #28600, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #55200, lsl #0
	movk x6, #4027, lsl #16
	movk x6, #17468, lsl #32
	movk x6, #43462, lsl #48
	movz x7, #63574, lsl #0
	movk x7, #25177, lsl #16
	movk x7, #13251, lsl #32
	movk x7, #56356, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #64, lsl #0
	dup v4.16b, w6
	movz x6, #128, lsl #0
	dup v5.16b, w6
	movz x6, #192, lsl #0
	dup v6.16b, w6
	movz x19, #0, lsl #0
	movk x19, #16, lsl #32
	movk x19, #32, lsl #48
	movz x20, #8208, lsl #0
	movk x20, #2064, lsl #16
	movk x20, #4096, lsl #32
	movk x20, #512, lsl #48
	movz x21, #1026, lsl #0
	movk x21, #288, lsl #32
	movk x21, #256, lsl #48
	movz x22, #2080, lsl #0
	movk x22, #1282, lsl #16
	movk x22, #2048, lsl #32
	movk x22, #8198, lsl #48
	movz x23, #0, lsl #0
	movk x23, #4, lsl #16
	movz x24, #0, lsl #0
	movk x24, #2048, lsl #48
	movz x25, #257, lsl #0
	movk x25, #512, lsl #16
	movk x25, #1032, lsl #32
	movk x25, #8, lsl #48
	movz x26, #0, lsl #0
	movk x26, #8201, lsl #16
	movk x26, #4096, lsl #48
	movz x27, #4608, lsl #0
	movk x27, #4096, lsl #16
	movk x27, #517, lsl #32
	movk x27, #1, lsl #48
	movz x0, #4, lsl #0
	movk x0, #32, lsl #16
	movk x0, #1024, lsl #48
	movz x8, #8, lsl #0
	movk x8, #8194, lsl #32
	movk x8, #16, lsl #48
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x11, x5, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #1
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #2
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #3
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #6
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #7
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #9
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #11
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #12
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #15
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #16
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4, lsl #0
	ror x6, x5, #18
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #20
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #512, lsl #0
	ror x6, x5, #21
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2, lsl #0
	ror x6, x5, #27
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #29
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #31
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #36
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #37
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #38
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #40
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #43
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #44
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #46
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #47
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #49
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #52
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #53
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #55
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #56
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #57
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #58
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #61
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #62
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	ror x12, x5, #1
	and x12, x12, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #2
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #3
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #4
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #7
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #8
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #11
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #12
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #13
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #16
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #17
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4, lsl #0
	ror x6, x5, #19
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #21
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #512, lsl #0
	ror x6, x5, #22
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2, lsl #0
	ror x6, x5, #28
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #31
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #32
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #37
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #38
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #39
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #41
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #44
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #45
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #47
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #48
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #50
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #53
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #54
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #56
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #57
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #58
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #59
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #62
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #63
	and x6, x6, x7
	eor x12, x12, x6
	add x10, x15, #0
	movz x16, #8, lsl #0
28:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 28b
	add x10, x10, #120
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
29:
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 29b
	add x10, x10, #136
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
210:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 210b
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x5, x12, x7
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	ror x6, x12, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #32
	ror x6, x12, #3
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #64, lsl #0
	movk x7, #16, lsl #48
	ror x6, x12, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #48
	ror x6, x12, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x12, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x12, #9
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #256, lsl #0
	ror x6, x12, #11
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x12, #15
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1024, lsl #0
	ror x6, x12, #17
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1, lsl #0
	ror x6, x12, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #48
	ror x6, x12, #21
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4, lsl #0
	ror x6, x12, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x12, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x12, #28
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x12, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #32
	ror x6, x12, #34
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x12, #37
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #16
	ror x6, x12, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #48
	ror x6, x12, #44
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x12, #46
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #32
	ror x6, x12, #48
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #16
	ror x6, x12, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #32
	ror x6, x12, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x12, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4096, lsl #0
	ror x6, x12, #55
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	ror x6, x12, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #48
	ror x6, x12, #58
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #16384, lsl #0
	ror x6, x12, #61
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x12, #63
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x11, #1
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x11, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #128, lsl #0
	movk x7, #32, lsl #48
	ror x6, x11, #5
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #48
	ror x6, x11, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x11, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x11, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #512, lsl #0
	ror x6, x11, #10
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x11, #14
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2048, lsl #0
	ror x6, x11, #16
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2, lsl #0
	ror x6, x11, #19
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #48
	ror x6, x11, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8, lsl #0
	ror x6, x11, #25
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x11, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #32
	ror x6, x11, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #48
	ror x6, x11, #32
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #32
	ror x6, x11, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	ror x6, x11, #36
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #16
	ror x6, x11, #42
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #48
	ror x6, x11, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	ror x6, x11, #45
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x11, #47
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #16
	ror x6, x11, #51
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #32
	ror x6, x11, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x11, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8192, lsl #0
	ror x6, x11, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x11, #56
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #48
	ror x6, x11, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32768, lsl #0
	ror x6, x11, #60
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x11, #62
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32, lsl #0
	movk x7, #8, lsl #48
	ror x6, x11, #63
	and x6, x6, x7
	eor x5, x5, x6
	ldr x19, [x15, #384]
	ldr x20, [x15, #392]
	ldr x21, [x15, #400]
	ldr x22, [x15, #408]
	ldr x23, [x15, #416]
	ldr x24, [x15, #424]
	ldr x25, [x15, #432]
	ldr x26, [x15, #440]
	ldr x27, [x15, #448]
	rev x5, x5
	str x5, [x1, #0]
	add sp, sp, #640
	ret
	.p2align 6
