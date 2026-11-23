// The functions of `src/internal/vg_brainpoolp512r1_validate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_validate:
	std %r31, 2944(%r3)
	mflr %r0
	std %r0, 2952(%r3)
	li %r4, 2240
	li %r5, 2176
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2304
	li %r5, 2368
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2432
	li %r5, 2304
	li %r6, 2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2240
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2752
	li %r5, 2688
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 448
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2752
	li %r6, 2688
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2752
	li %r5, 2496
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2688
	li %r5, 2432
	li %r6, 2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r5, 2688(%r3)
	ld %r4, 2696(%r3)
	or %r5, %r5, %r4
	ld %r4, 2704(%r3)
	or %r5, %r5, %r4
	ld %r4, 2712(%r3)
	or %r5, %r5, %r4
	ld %r4, 2720(%r3)
	or %r5, %r5, %r4
	ld %r4, 2728(%r3)
	or %r5, %r5, %r4
	ld %r4, 2736(%r3)
	or %r5, %r5, %r4
	ld %r4, 2744(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	li %r4, 0
	subf %r5, %r5, %r4
	addi %r5, %r5, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 576(%r3)
	ld %r5, 2240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2496(%r3)
	ld %r4, 584(%r3)
	ld %r5, 2248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2504(%r3)
	ld %r4, 592(%r3)
	ld %r5, 2256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2512(%r3)
	ld %r4, 600(%r3)
	ld %r5, 2264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2520(%r3)
	ld %r4, 608(%r3)
	ld %r5, 2272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2528(%r3)
	ld %r4, 616(%r3)
	ld %r5, 2280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2536(%r3)
	ld %r4, 624(%r3)
	ld %r5, 2288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2544(%r3)
	ld %r4, 632(%r3)
	ld %r5, 2296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2552(%r3)
	ld %r4, 640(%r3)
	ld %r5, 2304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2816(%r3)
	ld %r4, 648(%r3)
	ld %r5, 2312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2824(%r3)
	ld %r4, 656(%r3)
	ld %r5, 2320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2832(%r3)
	ld %r4, 664(%r3)
	ld %r5, 2328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2840(%r3)
	ld %r4, 672(%r3)
	ld %r5, 2336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2848(%r3)
	ld %r4, 680(%r3)
	ld %r5, 2344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2856(%r3)
	ld %r4, 688(%r3)
	ld %r5, 2352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2864(%r3)
	ld %r4, 696(%r3)
	ld %r5, 2360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2872(%r3)
	ld %r0, 2952(%r3)
	mtlr %r0
	ld %r31, 2944(%r3)
	blr
