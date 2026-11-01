// The functions of `src/p192_point.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_point_add:
	mflr %r0
	std %r0, 3696(%r3)
	li %r4, 3760
	li %r5, 3504
	li %r6, 3576
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3528
	li %r6, 3600
	bl {vg_p192_mul_mod_p}
	li %r4, 3808
	li %r5, 3552
	li %r6, 3624
	bl {vg_p192_mul_mod_p}
	li %r4, 3832
	li %r5, 3504
	li %r6, 3528
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3576
	li %r6, 3600
	bl {vg_p192_add_mod_p}
	li %r4, 3832
	li %r5, 3832
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3760
	li %r6, 3784
	bl {vg_p192_add_mod_p}
	li %r4, 3832
	li %r5, 3832
	li %r6, 3856
	bl {vg_p192_sub_mod_p}
	li %r4, 3856
	li %r5, 3504
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3576
	li %r6, 3624
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3880
	bl {vg_p192_mul_mod_p}
	li %r4, 3880
	li %r5, 3760
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3880
	bl {vg_p192_sub_mod_p}
	li %r4, 3880
	li %r5, 3528
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3432
	li %r5, 3600
	li %r6, 3624
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3880
	li %r6, 3432
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3784
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3880
	li %r6, 3432
	bl {vg_p192_sub_mod_p}
	li %r4, 3480
	li %r5, 3648
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3672
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3432
	li %r6, 3480
	bl {vg_p192_add_mod_p}
	li %r4, 3432
	li %r5, 3784
	li %r6, 3480
	bl {vg_p192_sub_mod_p}
	li %r4, 3480
	li %r5, 3784
	li %r6, 3480
	bl {vg_p192_add_mod_p}
	li %r4, 3456
	li %r5, 3432
	li %r6, 3480
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3760
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3784
	li %r5, 3784
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3672
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3784
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3808
	li %r5, 3760
	li %r6, 3808
	bl {vg_p192_sub_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3760
	li %r5, 3784
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3456
	li %r5, 3456
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3760
	li %r5, 3880
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3832
	li %r6, 3432
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3432
	li %r6, 3760
	bl {vg_p192_sub_mod_p}
	li %r4, 3760
	li %r5, 3832
	li %r6, 3784
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3880
	li %r6, 3480
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3480
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	ld %r0, 3696(%r3)
	mtlr %r0
	blr

vg_p192_point_double:
	mflr %r0
	std %r0, 3696(%r3)
	li %r4, 3760
	li %r5, 3504
	li %r6, 3504
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3528
	li %r6, 3528
	bl {vg_p192_mul_mod_p}
	li %r4, 3808
	li %r5, 3552
	li %r6, 3552
	bl {vg_p192_mul_mod_p}
	li %r4, 3832
	li %r5, 3504
	li %r6, 3528
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3504
	li %r6, 3528
	bl {vg_p192_add_mod_p}
	li %r4, 3832
	li %r5, 3832
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3760
	li %r6, 3784
	bl {vg_p192_add_mod_p}
	li %r4, 3832
	li %r5, 3832
	li %r6, 3856
	bl {vg_p192_sub_mod_p}
	li %r4, 3856
	li %r5, 3504
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3504
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3880
	bl {vg_p192_mul_mod_p}
	li %r4, 3880
	li %r5, 3760
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3880
	bl {vg_p192_sub_mod_p}
	li %r4, 3880
	li %r5, 3528
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3432
	li %r5, 3528
	li %r6, 3552
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3880
	li %r6, 3432
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3784
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3880
	li %r5, 3880
	li %r6, 3432
	bl {vg_p192_sub_mod_p}
	li %r4, 3480
	li %r5, 3648
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3672
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3432
	li %r6, 3480
	bl {vg_p192_add_mod_p}
	li %r4, 3432
	li %r5, 3784
	li %r6, 3480
	bl {vg_p192_sub_mod_p}
	li %r4, 3480
	li %r5, 3784
	li %r6, 3480
	bl {vg_p192_add_mod_p}
	li %r4, 3456
	li %r5, 3432
	li %r6, 3480
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3760
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3784
	li %r5, 3784
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3672
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3784
	li %r5, 3784
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3808
	li %r5, 3760
	li %r6, 3808
	bl {vg_p192_sub_mod_p}
	li %r4, 3808
	li %r5, 3648
	li %r6, 3808
	bl {vg_p192_mul_mod_p}
	li %r4, 3856
	li %r5, 3856
	li %r6, 3808
	bl {vg_p192_add_mod_p}
	li %r4, 3760
	li %r5, 3784
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3456
	li %r5, 3456
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	li %r4, 3760
	li %r5, 3880
	li %r6, 3856
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3832
	li %r6, 3432
	bl {vg_p192_mul_mod_p}
	li %r4, 3432
	li %r5, 3432
	li %r6, 3760
	bl {vg_p192_sub_mod_p}
	li %r4, 3760
	li %r5, 3832
	li %r6, 3784
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3880
	li %r6, 3480
	bl {vg_p192_mul_mod_p}
	li %r4, 3480
	li %r5, 3480
	li %r6, 3760
	bl {vg_p192_add_mod_p}
	ld %r0, 3696(%r3)
	mtlr %r0
	blr
