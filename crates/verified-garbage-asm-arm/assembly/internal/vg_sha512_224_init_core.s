// The functions of `src/internal/vg_sha512_224_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_224_init_core:
	movw r12, #19874
	movt r12, #6484
	str r12, [r0, #0]
	movw r12, #14280
	movt r12, #35901
	str r12, [r0, #4]
	movw r12, #54486
	movt r12, #35292
	str r12, [r0, #8]
	movw r12, #39270
	movt r12, #29665
	str r12, [r0, #12]
	movw r12, #40066
	movt r12, #13055
	str r12, [r0, #16]
	movw r12, #47022
	movt r12, #7674
	str r12, [r0, #20]
	movw r12, #40911
	movt r12, #22575
	str r12, [r0, #24]
	movw r12, #54548
	movt r12, #26525
	str r12, [r0, #28]
	movw r12, #19880
	movt r12, #31700
	str r12, [r0, #32]
	movw r12, #11113
	movt r12, #3949
	str r12, [r0, #36]
	movw r12, #35138
	movt r12, #1220
	str r12, [r0, #40]
	movw r12, #28531
	movt r12, #30691
	str r12, [r0, #44]
	movw r12, #14024
	movt r12, #27165
	str r12, [r0, #48]
	movw r12, #34216
	movt r12, #16285
	str r12, [r0, #52]
	movw r12, #37537
	movt r12, #37334
	str r12, [r0, #56]
	movw r12, #59053
	movt r12, #4370
	str r12, [r0, #60]
	bx lr
