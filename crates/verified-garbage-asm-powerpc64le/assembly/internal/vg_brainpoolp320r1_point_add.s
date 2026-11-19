// The functions of `src/internal/vg_brainpoolp320r1_point_add.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_point_add:
	mflr %r0
	std %r0, 3472(%r3)
	li %r4, 3536
	li %r5, 3152
	li %r6, 3272
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3576
	li %r5, 3192
	li %r6, 3312
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3616
	li %r5, 3232
	li %r6, 3352
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3656
	li %r5, 3152
	li %r6, 3192
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3696
	li %r5, 3272
	li %r6, 3312
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3656
	li %r5, 3656
	li %r6, 3696
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3696
	li %r5, 3536
	li %r6, 3576
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3656
	li %r5, 3656
	li %r6, 3696
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3696
	li %r5, 3152
	li %r6, 3232
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3736
	li %r5, 3272
	li %r6, 3352
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3696
	li %r5, 3696
	li %r6, 3736
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3736
	li %r5, 3536
	li %r6, 3616
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3696
	li %r5, 3696
	li %r6, 3736
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3736
	li %r5, 3192
	li %r6, 3232
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3032
	li %r5, 3312
	li %r6, 3352
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3736
	li %r5, 3736
	li %r6, 3032
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3032
	li %r5, 3576
	li %r6, 3616
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3736
	li %r5, 3736
	li %r6, 3032
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3112
	li %r5, 3392
	li %r6, 3696
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3032
	li %r5, 3432
	li %r6, 3616
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3112
	li %r5, 3032
	li %r6, 3112
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3032
	li %r5, 3576
	li %r6, 3112
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3112
	li %r5, 3576
	li %r6, 3112
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3072
	li %r5, 3032
	li %r6, 3112
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3576
	li %r5, 3536
	li %r6, 3536
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3576
	li %r5, 3576
	li %r6, 3536
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3616
	li %r5, 3392
	li %r6, 3616
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3696
	li %r5, 3432
	li %r6, 3696
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3576
	li %r5, 3576
	li %r6, 3616
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3616
	li %r5, 3536
	li %r6, 3616
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3616
	li %r5, 3392
	li %r6, 3616
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3696
	li %r5, 3696
	li %r6, 3616
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3536
	li %r5, 3576
	li %r6, 3696
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3072
	li %r5, 3072
	li %r6, 3536
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 3536
	li %r5, 3736
	li %r6, 3696
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3032
	li %r5, 3656
	li %r6, 3032
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3032
	li %r5, 3032
	li %r6, 3536
	bl {vg_brainpoolp320r1_sub_mod_p}
	li %r4, 3536
	li %r5, 3656
	li %r6, 3576
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3112
	li %r5, 3736
	li %r6, 3112
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 3112
	li %r5, 3112
	li %r6, 3536
	bl {vg_brainpoolp320r1_add_mod_p}
	ld %r0, 3472(%r3)
	mtlr %r0
	blr
