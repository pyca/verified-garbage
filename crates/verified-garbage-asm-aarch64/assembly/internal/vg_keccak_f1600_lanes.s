// The functions of `src/internal/vg_keccak_f1600_lanes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_lanes:
	dup v27.2d, x30
	adrp x16, {VG_KECCAK_RC}
	add x16, x16, {VG_KECCAK_RC}
	dup v28.2d, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #0]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #8]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #16]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #24]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #32]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #40]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #48]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #56]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #64]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #72]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #80]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #88]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #96]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #104]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #112]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #120]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #128]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #136]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #144]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #152]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #160]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #168]
	eor x0, x0, x16
	eor x16, x1, x6, ror #44
	eor x16, x16, x11, ror #51
	eor x16, x16, x19, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x5, ror #36
	eor x17, x17, x10, ror #8
	eor x17, x17, x15, ror #4
	eor x17, x17, x23, ror #33
	eor x30, x2, x7, ror #15
	eor x30, x30, x12, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x25, ror #12
	str x1, [x28, #0]
	eor x1, x3, x8, ror #36
	eor x1, x1, x13, ror #33
	eor x1, x1, x21, ror #8
	eor x1, x1, x26, ror #33
	str x11, [x28, #8]
	eor x11, x4, x9, ror #15
	eor x11, x11, x14, ror #48
	eor x11, x11, x22, ror #10
	eor x11, x11, x27, ror #14
	str x24, [x28, #16]
	eor x24, x11, x16, ror #14
	eor x16, x16, x1, ror #17
	eor x1, x1, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x11, ror #63
	eor x0, x0, x24, ror #31
	eor x5, x5, x24, ror #59
	eor x10, x10, x24, ror #23
	eor x15, x15, x24, ror #27
	eor x23, x23, x24, ror #62
	eor x2, x2, x16, ror #15
	eor x7, x7, x16
	eor x12, x12, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x25, x25, x16, ror #3
	eor x3, x3, x30, ror #31
	eor x8, x8, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x21, x21, x30, ror #23
	eor x26, x26, x30, ror #62
	eor x4, x4, x1, ror #33
	eor x9, x9, x1, ror #18
	eor x14, x14, x1, ror #49
	eor x22, x22, x1, ror #23
	eor x27, x27, x1, ror #19
	eor x11, x6, x17, ror #38
	bic x24, x21, x12, ror #49
	bic x16, x27, x21, ror #20
	bic x6, x0, x27, ror #31
	eor x6, x6, x21, ror #51
	bic x21, x11, x0, ror #18
	eor x21, x27, x21, ror #15
	eor x27, x16, x12, ror #5
	bic x16, x12, x11, ror #10
	eor x12, x11, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x11, x19, x17
	bic x24, x3, x25, ror #10
	bic x16, x9, x3, ror #10
	bic x19, x10, x9, ror #21
	eor x19, x3, x19, ror #33
	bic x3, x11, x10, ror #50
	eor x3, x9, x3, ror #57
	eor x9, x25, x16, ror #44
	bic x16, x25, x11, ror #37
	eor x25, x24, x11, ror #47
	eor x10, x16, x10, ror #23
	ldr x11, [x28, #0]
	eor x11, x11, x17, ror #18
	bic x24, x13, x7, ror #32
	bic x16, x22, x13, ror #39
	bic x1, x23, x22, ror #18
	eor x1, x1, x13, ror #57
	bic x13, x11, x23, ror #34
	eor x13, x22, x13, ror #12
	eor x22, x16, x7, ror #7
	bic x16, x7, x11, ror #5
	eor x7, x24, x11, ror #37
	eor x23, x23, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x26, x20, ror #31
	bic x30, x4, x26, ror #37
	bic x11, x5, x4, ror #4
	eor x11, x26, x11, ror #23
	bic x26, x24, x5, ror #41
	eor x26, x4, x26, ror #19
	eor x4, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x5, x5, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x8, x2, ror #52
	bic x17, x14, x8, ror #5
	bic x24, x15, x14, ror #13
	eor x24, x8, x24, ror #46
	bic x8, x16, x15, ror #48
	eor x8, x8, x14, ror #61
	eor x14, x2, x17, ror #7
	bic x17, x2, x16, ror #10
	eor x2, x30, x16, ror #62
	eor x15, x17, x15, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #176]
	eor x0, x0, x16
	eor x16, x12, x3, ror #44
	eor x16, x16, x22, ror #51
	eor x16, x16, x5, ror #18
	eor x16, x16, x24, ror #63
	eor x17, x0, x19, ror #36
	eor x17, x17, x7, ror #8
	eor x17, x17, x26, ror #4
	eor x17, x17, x14, ror #33
	eor x30, x27, x10, ror #15
	eor x30, x30, x1, ror #48
	eor x30, x30, x20, ror #56
	eor x30, x30, x8, ror #12
	str x12, [x28, #0]
	eor x12, x6, x25, ror #36
	eor x12, x12, x13, ror #33
	eor x12, x12, x4, ror #8
	eor x12, x12, x15, ror #33
	str x22, [x28, #8]
	eor x22, x21, x9, ror #15
	eor x22, x22, x23, ror #48
	eor x22, x22, x11, ror #10
	eor x22, x22, x2, ror #14
	str x24, [x28, #16]
	eor x24, x22, x16, ror #14
	eor x16, x16, x12, ror #17
	eor x12, x12, x17, ror #63
	eor x17, x17, x30, ror #30
	eor x30, x30, x22, ror #63
	eor x0, x0, x24, ror #31
	eor x19, x19, x24, ror #59
	eor x7, x7, x24, ror #23
	eor x26, x26, x24, ror #27
	eor x14, x14, x24, ror #62
	eor x27, x27, x16, ror #15
	eor x10, x10, x16
	eor x1, x1, x16, ror #31
	eor x20, x20, x16, ror #23
	eor x8, x8, x16, ror #3
	eor x6, x6, x30, ror #31
	eor x25, x25, x30, ror #59
	eor x13, x13, x30, ror #62
	eor x4, x4, x30, ror #23
	eor x15, x15, x30, ror #62
	eor x21, x21, x12, ror #33
	eor x9, x9, x12, ror #18
	eor x23, x23, x12, ror #49
	eor x11, x11, x12, ror #23
	eor x2, x2, x12, ror #19
	eor x22, x3, x17, ror #38
	bic x24, x4, x1, ror #49
	bic x16, x2, x4, ror #20
	bic x3, x0, x2, ror #31
	eor x3, x3, x4, ror #51
	bic x4, x22, x0, ror #18
	eor x4, x2, x4, ror #15
	eor x2, x16, x1, ror #5
	bic x16, x1, x22, ror #10
	eor x1, x22, x24, ror #5
	eor x0, x0, x16, ror #36
	eor x22, x5, x17
	bic x24, x6, x8, ror #10
	bic x16, x9, x6, ror #10
	bic x5, x7, x9, ror #21
	eor x5, x6, x5, ror #33
	bic x6, x22, x7, ror #50
	eor x6, x9, x6, ror #57
	eor x9, x8, x16, ror #44
	bic x16, x8, x22, ror #37
	eor x8, x24, x22, ror #47
	eor x7, x16, x7, ror #23
	ldr x22, [x28, #0]
	eor x22, x22, x17, ror #18
	bic x24, x13, x10, ror #32
	bic x16, x11, x13, ror #39
	bic x12, x14, x11, ror #18
	eor x12, x12, x13, ror #57
	bic x13, x22, x14, ror #34
	eor x13, x11, x13, ror #12
	eor x11, x16, x10, ror #7
	bic x16, x10, x22, ror #5
	eor x10, x24, x22, ror #37
	eor x14, x14, x16, ror #25
	ldr x24, [x28, #8]
	eor x24, x24, x17, ror #31
	bic x16, x15, x20, ror #31
	bic x30, x21, x15, ror #37
	bic x22, x19, x21, ror #4
	eor x22, x15, x22, ror #23
	bic x15, x24, x19, ror #41
	eor x15, x21, x15, ror #19
	eor x21, x20, x30, ror #60
	bic x30, x20, x24, ror #15
	eor x20, x24, x16, ror #18
	eor x19, x19, x30, ror #8
	ldr x16, [x28, #16]
	eor x16, x16, x17, ror #19
	bic x30, x25, x27, ror #52
	bic x17, x23, x25, ror #5
	bic x24, x26, x23, ror #13
	eor x24, x25, x24, ror #46
	bic x25, x16, x26, ror #48
	eor x25, x25, x23, ror #61
	eor x23, x27, x17, ror #7
	bic x17, x27, x16, ror #10
	eor x27, x30, x16, ror #62
	eor x26, x17, x26, ror #58
	umov x16, v28.d[0]
	ldr x16, [x16, #184]
	eor x0, x0, x16
	umov x30, v27.d[0]
	ret
	.p2align 6
