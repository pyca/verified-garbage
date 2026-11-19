// The functions of `src/internal/vg_sha512_256_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_256_init_core:
	movw r12, #63276
	movt r12, #64555
	str r12, [r0, #0]
	movw r12, #8596
	movt r12, #8753
	str r12, [r0, #4]
	movw r12, #25794
	movt r12, #51276
	str r12, [r0, #8]
	movw r12, #24483
	movt r12, #40789
	str r12, [r0, #12]
	movw r12, #45393
	movt r12, #28499
	str r12, [r0, #16]
	movw r12, #47211
	movt r12, #9107
	str r12, [r0, #20]
	movw r12, #60093
	movt r12, #22848
	str r12, [r0, #24]
	movw r12, #30489
	movt r12, #38456
	str r12, [r0, #28]
	movw r12, #65507
	movt r12, #43150
	str r12, [r0, #32]
	movw r12, #16098
	movt r12, #38440
	str r12, [r0, #36]
	movw r12, #14738
	movt r12, #21382
	str r12, [r0, #40]
	movw r12, #7717
	movt r12, #48734
	str r12, [r0, #44]
	movw r12, #47274
	movt r12, #11397
	str r12, [r0, #48]
	movw r12, #39420
	movt r12, #11009
	str r12, [r0, #52]
	movw r12, #11426
	movt r12, #33221
	str r12, [r0, #56]
	movw r12, #11740
	movt r12, #3767
	str r12, [r0, #60]
	bx lr
