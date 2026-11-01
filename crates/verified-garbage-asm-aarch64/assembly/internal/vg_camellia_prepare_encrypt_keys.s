// The functions of `src/internal/vg_camellia_prepare_encrypt_keys.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_prepare_encrypt_keys:
	add x5, x2, #0
	add x9, x21, #0
	movz x21, #33392, lsl #0
	movk x21, #60460, lsl #16
	movk x21, #10163, lsl #32
	movk x21, #58816, lsl #48
	str x21, [x5, #0]
	movz x21, #34276, lsl #0
	movk x21, #13655, lsl #16
	movk x21, #3306, lsl #32
	movk x21, #16814, lsl #48
	str x21, [x5, #8]
	movz x21, #61219, lsl #0
	movk x21, #37739, lsl #16
	movk x21, #6469, lsl #32
	movk x21, #8613, lsl #48
	str x21, [x5, #16]
	movz x21, #3821, lsl #0
	movk x21, #20047, lsl #16
	movk x21, #25885, lsl #32
	movk x21, #48530, lsl #48
	str x21, [x5, #24]
	movz x21, #47238, lsl #0
	movk x21, #36783, lsl #16
	movk x21, #60284, lsl #32
	movk x21, #52767, lsl #48
	str x21, [x5, #32]
	movz x21, #12350, lsl #0
	movk x21, #24540, lsl #16
	movk x21, #50526, lsl #32
	movk x21, #6667, lsl #48
	str x21, [x5, #40]
	movz x21, #57766, lsl #0
	movk x21, #51769, lsl #16
	movk x21, #18389, lsl #32
	movk x21, #15709, lsl #48
	str x21, [x5, #48]
	movz x21, #473, lsl #0
	movk x21, #54874, lsl #16
	movk x21, #22097, lsl #32
	movk x21, #19820, lsl #48
	str x21, [x5, #56]
	movz x21, #3467, lsl #0
	movk x21, #26266, lsl #16
	movk x21, #52475, lsl #32
	movk x21, #11696, lsl #48
	str x21, [x5, #64]
	movz x21, #4724, lsl #0
	movk x21, #8235, lsl #16
	movk x21, #45552, lsl #32
	movk x21, #39300, lsl #48
	str x21, [x5, #72]
	movz x21, #19679, lsl #0
	movk x21, #49867, lsl #16
	movk x21, #32308, lsl #32
	movk x21, #1398, lsl #48
	str x21, [x5, #80]
	movz x21, #46957, lsl #0
	movk x21, #12713, lsl #16
	movk x21, #6097, lsl #32
	movk x21, #55044, lsl #48
	str x21, [x5, #88]
	movz x21, #22548, lsl #0
	movk x21, #24890, lsl #16
	movk x21, #7134, lsl #32
	movk x21, #7185, lsl #48
	str x21, [x5, #96]
	movz x21, #3890, lsl #0
	movk x21, #5788, lsl #16
	movk x21, #6227, lsl #32
	movk x21, #8946, lsl #48
	str x21, [x5, #104]
	movz x21, #17662, lsl #0
	movk x21, #45775, lsl #16
	movk x21, #46531, lsl #32
	movk x21, #37242, lsl #48
	str x21, [x5, #112]
	movz x21, #2084, lsl #0
	movk x21, #43240, lsl #16
	movk x21, #64608, lsl #32
	movk x21, #20585, lsl #48
	str x21, [x5, #120]
	movz x21, #53418, lsl #0
	movk x21, #32160, lsl #16
	movk x21, #35233, lsl #32
	movk x21, #38754, lsl #48
	str x21, [x5, #128]
	movz x21, #23380, lsl #0
	movk x21, #38174, lsl #16
	movk x21, #65504, lsl #32
	movk x21, #53860, lsl #48
	str x21, [x5, #136]
	movz x21, #50192, lsl #0
	movk x21, #18432, lsl #16
	movk x21, #63395, lsl #32
	movk x21, #56181, lsl #48
	str x21, [x5, #144]
	movz x21, #906, lsl #0
	movk x21, #56038, lsl #16
	movk x21, #16137, lsl #32
	movk x21, #38109, lsl #48
	str x21, [x5, #152]
	movz x21, #23687, lsl #0
	movk x21, #643, lsl #16
	movk x21, #19149, lsl #32
	movk x21, #13200, lsl #48
	str x21, [x5, #160]
	movz x21, #26483, lsl #0
	movk x21, #62454, lsl #16
	movk x21, #32669, lsl #32
	movk x21, #58047, lsl #48
	str x21, [x5, #168]
	movz x21, #39762, lsl #0
	movk x21, #9944, lsl #16
	movk x21, #14280, lsl #32
	movk x21, #15302, lsl #48
	str x21, [x5, #176]
	movz x21, #38529, lsl #0
	movk x21, #19311, lsl #16
	movk x21, #48659, lsl #32
	movk x21, #11875, lsl #48
	str x21, [x5, #184]
	movz x21, #31209, lsl #0
	movk x21, #36007, lsl #16
	movk x21, #28319, lsl #32
	movk x21, #36540, lsl #48
	str x21, [x5, #192]
	movz x21, #62761, lsl #0
	movk x21, #46841, lsl #16
	movk x21, #64815, lsl #32
	movk x21, #22964, lsl #48
	str x21, [x5, #200]
	movz x21, #39032, lsl #0
	movk x21, #27142, lsl #16
	movk x21, #18151, lsl #32
	movk x21, #47729, lsl #48
	str x21, [x5, #208]
	movz x21, #9684, lsl #0
	movk x21, #17067, lsl #16
	movk x21, #41608, lsl #32
	movk x21, #64141, lsl #48
	str x21, [x5, #216]
	movz x21, #1906, lsl #0
	movk x21, #21945, lsl #16
	movk x21, #61176, lsl #32
	movk x21, #2732, lsl #48
	str x21, [x5, #224]
	movz x21, #18742, lsl #0
	movk x21, #26666, lsl #16
	movk x21, #14396, lsl #32
	movk x21, #42225, lsl #48
	str x21, [x5, #232]
	movz x21, #10304, lsl #0
	movk x21, #31699, lsl #16
	movk x21, #51643, lsl #32
	movk x21, #49475, lsl #48
	str x21, [x5, #240]
	movz x21, #58133, lsl #0
	movk x21, #62637, lsl #16
	movk x21, #51063, lsl #32
	movk x21, #40576, lsl #48
	str x21, [x5, #248]
	add x14, x0, #0
	add x15, x5, #256
	movz x17, #17, lsl #0
20:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 20b
	add x21, x9, #0
	ret
	.p2align 6
