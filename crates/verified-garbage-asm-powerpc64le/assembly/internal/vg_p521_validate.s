// The functions of `src/internal/vg_p521_validate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_validate:
	std %r31, 3304(%r3)
	mflr %r0
	std %r0, 3312(%r3)
	li %r4, 2512
	li %r5, 2440
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 2584
	li %r5, 2656
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 2728
	li %r5, 2584
	li %r6, 2584
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2512
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3088
	li %r5, 3016
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 496
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3088
	li %r6, 3016
	bl {vg_p521_add_mod_p}
	li %r4, 3088
	li %r5, 2800
	li %r6, 2944
	bl {vg_p521_add_mod_p}
	li %r4, 3016
	li %r5, 2728
	li %r6, 3088
	bl {vg_p521_sub_mod_p}
	ld %r5, 3016(%r3)
	ld %r4, 3024(%r3)
	or %r5, %r5, %r4
	ld %r4, 3032(%r3)
	or %r5, %r5, %r4
	ld %r4, 3040(%r3)
	or %r5, %r5, %r4
	ld %r4, 3048(%r3)
	or %r5, %r5, %r4
	ld %r4, 3056(%r3)
	or %r5, %r5, %r4
	ld %r4, 3064(%r3)
	or %r5, %r5, %r4
	ld %r4, 3072(%r3)
	or %r5, %r5, %r4
	ld %r4, 3080(%r3)
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
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	ld %r4, 640(%r3)
	ld %r5, 2512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2800(%r3)
	ld %r4, 648(%r3)
	ld %r5, 2520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2808(%r3)
	ld %r4, 656(%r3)
	ld %r5, 2528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2816(%r3)
	ld %r4, 664(%r3)
	ld %r5, 2536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2824(%r3)
	ld %r4, 672(%r3)
	ld %r5, 2544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2832(%r3)
	ld %r4, 680(%r3)
	ld %r5, 2552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2840(%r3)
	ld %r4, 688(%r3)
	ld %r5, 2560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2848(%r3)
	ld %r4, 696(%r3)
	ld %r5, 2568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2856(%r3)
	ld %r4, 704(%r3)
	ld %r5, 2576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2864(%r3)
	ld %r4, 712(%r3)
	ld %r5, 2584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3160(%r3)
	ld %r4, 720(%r3)
	ld %r5, 2592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3168(%r3)
	ld %r4, 728(%r3)
	ld %r5, 2600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3176(%r3)
	ld %r4, 736(%r3)
	ld %r5, 2608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3184(%r3)
	ld %r4, 744(%r3)
	ld %r5, 2616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3192(%r3)
	ld %r4, 752(%r3)
	ld %r5, 2624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3200(%r3)
	ld %r4, 760(%r3)
	ld %r5, 2632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3208(%r3)
	ld %r4, 768(%r3)
	ld %r5, 2640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3216(%r3)
	ld %r4, 776(%r3)
	ld %r5, 2648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3224(%r3)
	ld %r0, 3312(%r3)
	mtlr %r0
	ld %r31, 3304(%r3)
	blr
