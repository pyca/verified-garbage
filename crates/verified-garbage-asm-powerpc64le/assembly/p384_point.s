// The functions of `src/p384_point.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_point_add:
	mflr %r0
	std %r0, 3360(%r3)
	li %r4, 3424
	li %r5, 2976
	li %r6, 3120
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3024
	li %r6, 3168
	bl {vg_p384_mul_mod_p}
	li %r4, 3520
	li %r5, 3072
	li %r6, 3216
	bl {vg_p384_mul_mod_p}
	li %r4, 3568
	li %r5, 2976
	li %r6, 3024
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 3120
	li %r6, 3168
	bl {vg_p384_add_mod_p}
	li %r4, 3568
	li %r5, 3568
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3424
	li %r6, 3472
	bl {vg_p384_add_mod_p}
	li %r4, 3568
	li %r5, 3568
	li %r6, 3616
	bl {vg_p384_sub_mod_p}
	li %r4, 3616
	li %r5, 2976
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 3120
	li %r6, 3216
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3664
	bl {vg_p384_mul_mod_p}
	li %r4, 3664
	li %r5, 3424
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3664
	bl {vg_p384_sub_mod_p}
	li %r4, 3664
	li %r5, 3024
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 2832
	li %r5, 3168
	li %r6, 3216
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 3664
	li %r6, 2832
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3472
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 3664
	li %r6, 2832
	bl {vg_p384_sub_mod_p}
	li %r4, 2928
	li %r5, 3264
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3312
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 2832
	li %r6, 2928
	bl {vg_p384_add_mod_p}
	li %r4, 2832
	li %r5, 3472
	li %r6, 2928
	bl {vg_p384_sub_mod_p}
	li %r4, 2928
	li %r5, 3472
	li %r6, 2928
	bl {vg_p384_add_mod_p}
	li %r4, 2880
	li %r5, 2832
	li %r6, 2928
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3424
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3472
	li %r5, 3472
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3520
	li %r5, 3264
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3312
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3472
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3520
	li %r5, 3424
	li %r6, 3520
	bl {vg_p384_sub_mod_p}
	li %r4, 3520
	li %r5, 3264
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3424
	li %r5, 3472
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2880
	li %r5, 2880
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3424
	li %r5, 3664
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3568
	li %r6, 2832
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 2832
	li %r6, 3424
	bl {vg_p384_sub_mod_p}
	li %r4, 3424
	li %r5, 3568
	li %r6, 3472
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 3664
	li %r6, 2928
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 2928
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	ld %r0, 3360(%r3)
	mtlr %r0
	blr

vg_p384_point_double:
	mflr %r0
	std %r0, 3360(%r3)
	li %r4, 3424
	li %r5, 2976
	li %r6, 2976
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3024
	li %r6, 3024
	bl {vg_p384_mul_mod_p}
	li %r4, 3520
	li %r5, 3072
	li %r6, 3072
	bl {vg_p384_mul_mod_p}
	li %r4, 3568
	li %r5, 2976
	li %r6, 3024
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 2976
	li %r6, 3024
	bl {vg_p384_add_mod_p}
	li %r4, 3568
	li %r5, 3568
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3424
	li %r6, 3472
	bl {vg_p384_add_mod_p}
	li %r4, 3568
	li %r5, 3568
	li %r6, 3616
	bl {vg_p384_sub_mod_p}
	li %r4, 3616
	li %r5, 2976
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 2976
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3664
	bl {vg_p384_mul_mod_p}
	li %r4, 3664
	li %r5, 3424
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3664
	bl {vg_p384_sub_mod_p}
	li %r4, 3664
	li %r5, 3024
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 2832
	li %r5, 3024
	li %r6, 3072
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 3664
	li %r6, 2832
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3472
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3664
	li %r5, 3664
	li %r6, 2832
	bl {vg_p384_sub_mod_p}
	li %r4, 2928
	li %r5, 3264
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3312
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 2832
	li %r6, 2928
	bl {vg_p384_add_mod_p}
	li %r4, 2832
	li %r5, 3472
	li %r6, 2928
	bl {vg_p384_sub_mod_p}
	li %r4, 2928
	li %r5, 3472
	li %r6, 2928
	bl {vg_p384_add_mod_p}
	li %r4, 2880
	li %r5, 2832
	li %r6, 2928
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3424
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3472
	li %r5, 3472
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3520
	li %r5, 3264
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3312
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 3472
	li %r5, 3472
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3520
	li %r5, 3424
	li %r6, 3520
	bl {vg_p384_sub_mod_p}
	li %r4, 3520
	li %r5, 3264
	li %r6, 3520
	bl {vg_p384_mul_mod_p}
	li %r4, 3616
	li %r5, 3616
	li %r6, 3520
	bl {vg_p384_add_mod_p}
	li %r4, 3424
	li %r5, 3472
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2880
	li %r5, 2880
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	li %r4, 3424
	li %r5, 3664
	li %r6, 3616
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 3568
	li %r6, 2832
	bl {vg_p384_mul_mod_p}
	li %r4, 2832
	li %r5, 2832
	li %r6, 3424
	bl {vg_p384_sub_mod_p}
	li %r4, 3424
	li %r5, 3568
	li %r6, 3472
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 3664
	li %r6, 2928
	bl {vg_p384_mul_mod_p}
	li %r4, 2928
	li %r5, 2928
	li %r6, 3424
	bl {vg_p384_add_mod_p}
	ld %r0, 3360(%r3)
	mtlr %r0
	blr
