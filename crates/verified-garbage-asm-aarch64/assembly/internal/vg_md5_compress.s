// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	cbz x2, 20f
22:
	ldr w4, [x0, #0]
	ldr w5, [x0, #4]
	ldr w6, [x0, #8]
	ldr w7, [x0, #12]
	movz w14, #65535, lsl #0
	movk w14, #65535, lsl #16
	ldr w13, [x1, #0]
	add w4, w4, w13
	movz w13, #42104, lsl #0
	movk w13, #55146, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w4, w4, w12
	ror w4, w4, #25
	add w4, w4, w5
	ldr w13, [x1, #4]
	add w7, w7, w13
	movz w13, #46934, lsl #0
	movk w13, #59591, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	ror w7, w7, #20
	add w7, w7, w4
	ldr w13, [x1, #8]
	add w6, w6, w13
	movz w13, #28891, lsl #0
	movk w13, #9248, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	and w12, w12, w7
	eor w12, w12, w5
	add w6, w6, w12
	ror w6, w6, #15
	add w6, w6, w7
	ldr w13, [x1, #12]
	add w5, w5, w13
	movz w13, #52974, lsl #0
	movk w13, #49597, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	and w12, w12, w6
	eor w12, w12, w4
	add w5, w5, w12
	ror w5, w5, #10
	add w5, w5, w6
	ldr w13, [x1, #16]
	add w4, w4, w13
	movz w13, #4015, lsl #0
	movk w13, #62844, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w4, w4, w12
	ror w4, w4, #25
	add w4, w4, w5
	ldr w13, [x1, #20]
	add w7, w7, w13
	movz w13, #50730, lsl #0
	movk w13, #18311, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	ror w7, w7, #20
	add w7, w7, w4
	ldr w13, [x1, #24]
	add w6, w6, w13
	movz w13, #17939, lsl #0
	movk w13, #43056, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	and w12, w12, w7
	eor w12, w12, w5
	add w6, w6, w12
	ror w6, w6, #15
	add w6, w6, w7
	ldr w13, [x1, #28]
	add w5, w5, w13
	movz w13, #38145, lsl #0
	movk w13, #64838, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	and w12, w12, w6
	eor w12, w12, w4
	add w5, w5, w12
	ror w5, w5, #10
	add w5, w5, w6
	ldr w13, [x1, #32]
	add w4, w4, w13
	movz w13, #39128, lsl #0
	movk w13, #27008, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w4, w4, w12
	ror w4, w4, #25
	add w4, w4, w5
	ldr w13, [x1, #36]
	add w7, w7, w13
	movz w13, #63407, lsl #0
	movk w13, #35652, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	ror w7, w7, #20
	add w7, w7, w4
	ldr w13, [x1, #40]
	add w6, w6, w13
	movz w13, #23473, lsl #0
	movk w13, #65535, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	and w12, w12, w7
	eor w12, w12, w5
	add w6, w6, w12
	ror w6, w6, #15
	add w6, w6, w7
	ldr w13, [x1, #44]
	add w5, w5, w13
	movz w13, #55230, lsl #0
	movk w13, #35164, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	and w12, w12, w6
	eor w12, w12, w4
	add w5, w5, w12
	ror w5, w5, #10
	add w5, w5, w6
	ldr w13, [x1, #48]
	add w4, w4, w13
	movz w13, #4386, lsl #0
	movk w13, #27536, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w4, w4, w12
	ror w4, w4, #25
	add w4, w4, w5
	ldr w13, [x1, #52]
	add w7, w7, w13
	movz w13, #29075, lsl #0
	movk w13, #64920, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	ror w7, w7, #20
	add w7, w7, w4
	ldr w13, [x1, #56]
	add w6, w6, w13
	movz w13, #17294, lsl #0
	movk w13, #42617, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	and w12, w12, w7
	eor w12, w12, w5
	add w6, w6, w12
	ror w6, w6, #15
	add w6, w6, w7
	ldr w13, [x1, #60]
	add w5, w5, w13
	movz w13, #2081, lsl #0
	movk w13, #18868, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	and w12, w12, w6
	eor w12, w12, w4
	add w5, w5, w12
	ror w5, w5, #10
	add w5, w5, w6
	ldr w13, [x1, #4]
	add w4, w4, w13
	movz w13, #9570, lsl #0
	movk w13, #63006, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	and w12, w12, w6
	add w4, w4, w12
	and w12, w7, w5
	add w4, w4, w12
	ror w4, w4, #27
	add w4, w4, w5
	ldr w13, [x1, #24]
	add w7, w7, w13
	movz w13, #45888, lsl #0
	movk w13, #49216, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	and w12, w12, w5
	add w7, w7, w12
	and w12, w6, w4
	add w7, w7, w12
	ror w7, w7, #23
	add w7, w7, w4
	ldr w13, [x1, #44]
	add w6, w6, w13
	movz w13, #23121, lsl #0
	movk w13, #9822, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	and w12, w12, w4
	add w6, w6, w12
	and w12, w5, w7
	add w6, w6, w12
	ror w6, w6, #18
	add w6, w6, w7
	ldr w13, [x1, #0]
	add w5, w5, w13
	movz w13, #51114, lsl #0
	movk w13, #59830, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	and w12, w12, w7
	add w5, w5, w12
	and w12, w4, w6
	add w5, w5, w12
	ror w5, w5, #12
	add w5, w5, w6
	ldr w13, [x1, #20]
	add w4, w4, w13
	movz w13, #4189, lsl #0
	movk w13, #54831, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	and w12, w12, w6
	add w4, w4, w12
	and w12, w7, w5
	add w4, w4, w12
	ror w4, w4, #27
	add w4, w4, w5
	ldr w13, [x1, #40]
	add w7, w7, w13
	movz w13, #5203, lsl #0
	movk w13, #580, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	and w12, w12, w5
	add w7, w7, w12
	and w12, w6, w4
	add w7, w7, w12
	ror w7, w7, #23
	add w7, w7, w4
	ldr w13, [x1, #60]
	add w6, w6, w13
	movz w13, #59009, lsl #0
	movk w13, #55457, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	and w12, w12, w4
	add w6, w6, w12
	and w12, w5, w7
	add w6, w6, w12
	ror w6, w6, #18
	add w6, w6, w7
	ldr w13, [x1, #16]
	add w5, w5, w13
	movz w13, #64456, lsl #0
	movk w13, #59347, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	and w12, w12, w7
	add w5, w5, w12
	and w12, w4, w6
	add w5, w5, w12
	ror w5, w5, #12
	add w5, w5, w6
	ldr w13, [x1, #36]
	add w4, w4, w13
	movz w13, #52710, lsl #0
	movk w13, #8673, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	and w12, w12, w6
	add w4, w4, w12
	and w12, w7, w5
	add w4, w4, w12
	ror w4, w4, #27
	add w4, w4, w5
	ldr w13, [x1, #56]
	add w7, w7, w13
	movz w13, #2006, lsl #0
	movk w13, #49975, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	and w12, w12, w5
	add w7, w7, w12
	and w12, w6, w4
	add w7, w7, w12
	ror w7, w7, #23
	add w7, w7, w4
	ldr w13, [x1, #12]
	add w6, w6, w13
	movz w13, #3463, lsl #0
	movk w13, #62677, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	and w12, w12, w4
	add w6, w6, w12
	and w12, w5, w7
	add w6, w6, w12
	ror w6, w6, #18
	add w6, w6, w7
	ldr w13, [x1, #32]
	add w5, w5, w13
	movz w13, #5357, lsl #0
	movk w13, #17754, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	and w12, w12, w7
	add w5, w5, w12
	and w12, w4, w6
	add w5, w5, w12
	ror w5, w5, #12
	add w5, w5, w6
	ldr w13, [x1, #52]
	add w4, w4, w13
	movz w13, #59653, lsl #0
	movk w13, #43491, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	and w12, w12, w6
	add w4, w4, w12
	and w12, w7, w5
	add w4, w4, w12
	ror w4, w4, #27
	add w4, w4, w5
	ldr w13, [x1, #8]
	add w7, w7, w13
	movz w13, #41976, lsl #0
	movk w13, #64751, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	and w12, w12, w5
	add w7, w7, w12
	and w12, w6, w4
	add w7, w7, w12
	ror w7, w7, #23
	add w7, w7, w4
	ldr w13, [x1, #28]
	add w6, w6, w13
	movz w13, #729, lsl #0
	movk w13, #26479, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	and w12, w12, w4
	add w6, w6, w12
	and w12, w5, w7
	add w6, w6, w12
	ror w6, w6, #18
	add w6, w6, w7
	ldr w13, [x1, #48]
	add w5, w5, w13
	movz w13, #19594, lsl #0
	movk w13, #36138, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	and w12, w12, w7
	add w5, w5, w12
	and w12, w4, w6
	add w5, w5, w12
	ror w5, w5, #12
	add w5, w5, w6
	ldr w13, [x1, #20]
	add w4, w4, w13
	movz w13, #14658, lsl #0
	movk w13, #65530, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	eor w12, w12, w5
	add w4, w4, w12
	ror w4, w4, #28
	add w4, w4, w5
	ldr w13, [x1, #32]
	add w7, w7, w13
	movz w13, #63105, lsl #0
	movk w13, #34673, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	eor w12, w12, w4
	add w7, w7, w12
	ror w7, w7, #21
	add w7, w7, w4
	ldr w13, [x1, #44]
	add w6, w6, w13
	movz w13, #24866, lsl #0
	movk w13, #28061, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	eor w12, w12, w7
	add w6, w6, w12
	ror w6, w6, #16
	add w6, w6, w7
	ldr w13, [x1, #56]
	add w5, w5, w13
	movz w13, #14348, lsl #0
	movk w13, #64997, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	eor w12, w12, w6
	add w5, w5, w12
	ror w5, w5, #9
	add w5, w5, w6
	ldr w13, [x1, #4]
	add w4, w4, w13
	movz w13, #59972, lsl #0
	movk w13, #42174, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	eor w12, w12, w5
	add w4, w4, w12
	ror w4, w4, #28
	add w4, w4, w5
	ldr w13, [x1, #16]
	add w7, w7, w13
	movz w13, #53161, lsl #0
	movk w13, #19422, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	eor w12, w12, w4
	add w7, w7, w12
	ror w7, w7, #21
	add w7, w7, w4
	ldr w13, [x1, #28]
	add w6, w6, w13
	movz w13, #19296, lsl #0
	movk w13, #63163, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	eor w12, w12, w7
	add w6, w6, w12
	ror w6, w6, #16
	add w6, w6, w7
	ldr w13, [x1, #40]
	add w5, w5, w13
	movz w13, #48240, lsl #0
	movk w13, #48831, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	eor w12, w12, w6
	add w5, w5, w12
	ror w5, w5, #9
	add w5, w5, w6
	ldr w13, [x1, #52]
	add w4, w4, w13
	movz w13, #32454, lsl #0
	movk w13, #10395, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	eor w12, w12, w5
	add w4, w4, w12
	ror w4, w4, #28
	add w4, w4, w5
	ldr w13, [x1, #0]
	add w7, w7, w13
	movz w13, #10234, lsl #0
	movk w13, #60065, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	eor w12, w12, w4
	add w7, w7, w12
	ror w7, w7, #21
	add w7, w7, w4
	ldr w13, [x1, #12]
	add w6, w6, w13
	movz w13, #12421, lsl #0
	movk w13, #54511, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	eor w12, w12, w7
	add w6, w6, w12
	ror w6, w6, #16
	add w6, w6, w7
	ldr w13, [x1, #24]
	add w5, w5, w13
	movz w13, #7429, lsl #0
	movk w13, #1160, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	eor w12, w12, w6
	add w5, w5, w12
	ror w5, w5, #9
	add w5, w5, w6
	ldr w13, [x1, #36]
	add w4, w4, w13
	movz w13, #53305, lsl #0
	movk w13, #55764, lsl #16
	add w4, w4, w13
	eor w12, w6, w7
	eor w12, w12, w5
	add w4, w4, w12
	ror w4, w4, #28
	add w4, w4, w5
	ldr w13, [x1, #48]
	add w7, w7, w13
	movz w13, #39397, lsl #0
	movk w13, #59099, lsl #16
	add w7, w7, w13
	eor w12, w5, w6
	eor w12, w12, w4
	add w7, w7, w12
	ror w7, w7, #21
	add w7, w7, w4
	ldr w13, [x1, #60]
	add w6, w6, w13
	movz w13, #31992, lsl #0
	movk w13, #8098, lsl #16
	add w6, w6, w13
	eor w12, w4, w5
	eor w12, w12, w7
	add w6, w6, w12
	ror w6, w6, #16
	add w6, w6, w7
	ldr w13, [x1, #8]
	add w5, w5, w13
	movz w13, #22117, lsl #0
	movk w13, #50348, lsl #16
	add w5, w5, w13
	eor w12, w7, w4
	eor w12, w12, w6
	add w5, w5, w12
	ror w5, w5, #9
	add w5, w5, w6
	ldr w13, [x1, #0]
	add w4, w4, w13
	movz w13, #8772, lsl #0
	movk w13, #62505, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	orr w12, w12, w5
	eor w12, w12, w6
	add w4, w4, w12
	ror w4, w4, #26
	add w4, w4, w5
	ldr w13, [x1, #28]
	add w7, w7, w13
	movz w13, #65431, lsl #0
	movk w13, #17194, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	orr w12, w12, w4
	eor w12, w12, w5
	add w7, w7, w12
	ror w7, w7, #22
	add w7, w7, w4
	ldr w13, [x1, #56]
	add w6, w6, w13
	movz w13, #9127, lsl #0
	movk w13, #43924, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	orr w12, w12, w7
	eor w12, w12, w4
	add w6, w6, w12
	ror w6, w6, #17
	add w6, w6, w7
	ldr w13, [x1, #20]
	add w5, w5, w13
	movz w13, #41017, lsl #0
	movk w13, #64659, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	orr w12, w12, w6
	eor w12, w12, w7
	add w5, w5, w12
	ror w5, w5, #11
	add w5, w5, w6
	ldr w13, [x1, #48]
	add w4, w4, w13
	movz w13, #22979, lsl #0
	movk w13, #25947, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	orr w12, w12, w5
	eor w12, w12, w6
	add w4, w4, w12
	ror w4, w4, #26
	add w4, w4, w5
	ldr w13, [x1, #12]
	add w7, w7, w13
	movz w13, #52370, lsl #0
	movk w13, #36620, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	orr w12, w12, w4
	eor w12, w12, w5
	add w7, w7, w12
	ror w7, w7, #22
	add w7, w7, w4
	ldr w13, [x1, #40]
	add w6, w6, w13
	movz w13, #62589, lsl #0
	movk w13, #65519, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	orr w12, w12, w7
	eor w12, w12, w4
	add w6, w6, w12
	ror w6, w6, #17
	add w6, w6, w7
	ldr w13, [x1, #4]
	add w5, w5, w13
	movz w13, #24017, lsl #0
	movk w13, #34180, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	orr w12, w12, w6
	eor w12, w12, w7
	add w5, w5, w12
	ror w5, w5, #11
	add w5, w5, w6
	ldr w13, [x1, #32]
	add w4, w4, w13
	movz w13, #32335, lsl #0
	movk w13, #28584, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	orr w12, w12, w5
	eor w12, w12, w6
	add w4, w4, w12
	ror w4, w4, #26
	add w4, w4, w5
	ldr w13, [x1, #60]
	add w7, w7, w13
	movz w13, #59104, lsl #0
	movk w13, #65068, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	orr w12, w12, w4
	eor w12, w12, w5
	add w7, w7, w12
	ror w7, w7, #22
	add w7, w7, w4
	ldr w13, [x1, #24]
	add w6, w6, w13
	movz w13, #17172, lsl #0
	movk w13, #41729, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	orr w12, w12, w7
	eor w12, w12, w4
	add w6, w6, w12
	ror w6, w6, #17
	add w6, w6, w7
	ldr w13, [x1, #52]
	add w5, w5, w13
	movz w13, #4513, lsl #0
	movk w13, #19976, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	orr w12, w12, w6
	eor w12, w12, w7
	add w5, w5, w12
	ror w5, w5, #11
	add w5, w5, w6
	ldr w13, [x1, #16]
	add w4, w4, w13
	movz w13, #32386, lsl #0
	movk w13, #63315, lsl #16
	add w4, w4, w13
	eor w12, w7, w14
	orr w12, w12, w5
	eor w12, w12, w6
	add w4, w4, w12
	ror w4, w4, #26
	add w4, w4, w5
	ldr w13, [x1, #44]
	add w7, w7, w13
	movz w13, #62005, lsl #0
	movk w13, #48442, lsl #16
	add w7, w7, w13
	eor w12, w6, w14
	orr w12, w12, w4
	eor w12, w12, w5
	add w7, w7, w12
	ror w7, w7, #22
	add w7, w7, w4
	ldr w13, [x1, #8]
	add w6, w6, w13
	movz w13, #53947, lsl #0
	movk w13, #10967, lsl #16
	add w6, w6, w13
	eor w12, w5, w14
	orr w12, w12, w7
	eor w12, w12, w4
	add w6, w6, w12
	ror w6, w6, #17
	add w6, w6, w7
	ldr w13, [x1, #36]
	add w5, w5, w13
	movz w13, #54161, lsl #0
	movk w13, #60294, lsl #16
	add w5, w5, w13
	eor w12, w4, w14
	orr w12, w12, w6
	eor w12, w12, w7
	add w5, w5, w12
	ror w5, w5, #11
	add w5, w5, w6
	ldr w12, [x0, #0]
	ldr w13, [x0, #4]
	ldr w14, [x0, #8]
	ldr w15, [x0, #12]
	add w4, w4, w12
	add w5, w5, w13
	add w6, w6, w14
	add w7, w7, w15
	str w4, [x0, #0]
	str w5, [x0, #4]
	str w6, [x0, #8]
	str w7, [x0, #12]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.p2align 6
