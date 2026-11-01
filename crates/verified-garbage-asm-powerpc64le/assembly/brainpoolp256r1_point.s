// The functions of `src/brainpoolp256r1_point.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_point_add:
	mflr %r0
	std %r0, 3584(%r3)
	li %r4, 3648
	li %r5, 3328
	li %r6, 3424
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3360
	li %r6, 3456
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3712
	li %r5, 3392
	li %r6, 3488
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3744
	li %r5, 3328
	li %r6, 3360
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3424
	li %r6, 3456
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3744
	li %r5, 3744
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3648
	li %r6, 3680
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3744
	li %r5, 3744
	li %r6, 3776
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3776
	li %r5, 3328
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3424
	li %r6, 3488
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3808
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3808
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3808
	li %r5, 3360
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3232
	li %r5, 3456
	li %r6, 3488
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3808
	li %r6, 3232
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3680
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3808
	li %r6, 3232
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3296
	li %r5, 3520
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3552
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3232
	li %r6, 3296
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3232
	li %r5, 3680
	li %r6, 3296
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3296
	li %r5, 3680
	li %r6, 3296
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3264
	li %r5, 3232
	li %r6, 3296
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3648
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3680
	li %r5, 3680
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3712
	li %r5, 3520
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3552
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3680
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3712
	li %r5, 3648
	li %r6, 3712
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3712
	li %r5, 3520
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3648
	li %r5, 3680
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3264
	li %r5, 3264
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3648
	li %r5, 3808
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3744
	li %r6, 3232
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3232
	li %r6, 3648
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3648
	li %r5, 3744
	li %r6, 3680
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3808
	li %r6, 3296
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3296
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	ld %r0, 3584(%r3)
	mtlr %r0
	blr

vg_brainpoolp256r1_point_double:
	mflr %r0
	std %r0, 3584(%r3)
	li %r4, 3648
	li %r5, 3328
	li %r6, 3328
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3360
	li %r6, 3360
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3712
	li %r5, 3392
	li %r6, 3392
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3744
	li %r5, 3328
	li %r6, 3360
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3328
	li %r6, 3360
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3744
	li %r5, 3744
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3648
	li %r6, 3680
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3744
	li %r5, 3744
	li %r6, 3776
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3776
	li %r5, 3328
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3328
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3808
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3808
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3808
	li %r5, 3360
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3232
	li %r5, 3360
	li %r6, 3392
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3808
	li %r6, 3232
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3680
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3808
	li %r5, 3808
	li %r6, 3232
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3296
	li %r5, 3520
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3552
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3232
	li %r6, 3296
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3232
	li %r5, 3680
	li %r6, 3296
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3296
	li %r5, 3680
	li %r6, 3296
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3264
	li %r5, 3232
	li %r6, 3296
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3648
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3680
	li %r5, 3680
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3712
	li %r5, 3520
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3552
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3680
	li %r5, 3680
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3712
	li %r5, 3648
	li %r6, 3712
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3712
	li %r5, 3520
	li %r6, 3712
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3776
	li %r5, 3776
	li %r6, 3712
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3648
	li %r5, 3680
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3264
	li %r5, 3264
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	li %r4, 3648
	li %r5, 3808
	li %r6, 3776
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3744
	li %r6, 3232
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3232
	li %r5, 3232
	li %r6, 3648
	bl {vg_brainpoolp256r1_sub_mod_p}
	li %r4, 3648
	li %r5, 3744
	li %r6, 3680
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3808
	li %r6, 3296
	bl {vg_brainpoolp256r1_mul_mod_p}
	li %r4, 3296
	li %r5, 3296
	li %r6, 3648
	bl {vg_brainpoolp256r1_add_mod_p}
	ld %r0, 3584(%r3)
	mtlr %r0
	blr
