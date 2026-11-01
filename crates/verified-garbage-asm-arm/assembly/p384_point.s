// The functions of `src/p384_point.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_point_add:
	mov r12, r0
	str lr, [r12, #3360]
	mov r0, r12
	movw r1, #3424
	movw r2, #2976
	movw r3, #3120
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3024
	movw r3, #3168
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3072
	movw r3, #3216
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3120
	movw r3, #3168
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3424
	movw r3, #3472
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3120
	movw r3, #3216
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3168
	movw r3, #3216
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3264
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3312
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3424
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3312
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3472
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2880
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3664
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3568
	movw r3, #2832
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #2832
	movw r3, #3424
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3568
	movw r3, #3472
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3664
	movw r3, #2928
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #2928
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	ldr lr, [r12, #3360]
	bx lr

vg_p384_point_double:
	mov r12, r0
	str lr, [r12, #3360]
	mov r0, r12
	movw r1, #3424
	movw r2, #2976
	movw r3, #2976
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3024
	movw r3, #3024
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3072
	movw r3, #3072
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3424
	movw r3, #3472
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3264
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3312
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3424
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3312
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3472
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2880
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3664
	movw r3, #3616
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3568
	movw r3, #2832
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #2832
	movw r3, #3424
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3568
	movw r3, #3472
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3664
	movw r3, #2928
	bl {vg_p384_mul_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #2928
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	ldr lr, [r12, #3360]
	bx lr

vg_p384_point_add_umaal:
	mov r12, r0
	str lr, [r12, #3360]
	mov r0, r12
	movw r1, #3424
	movw r2, #2976
	movw r3, #3120
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3024
	movw r3, #3168
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3520
	movw r2, #3072
	movw r3, #3216
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3568
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3120
	movw r3, #3168
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3424
	movw r3, #3472
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3120
	movw r3, #3216
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3664
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3168
	movw r3, #3216
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3264
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3312
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3424
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3312
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3472
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2880
	movw r2, #2880
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3664
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3568
	movw r3, #2832
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #2832
	movw r3, #3424
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3568
	movw r3, #3472
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #3664
	movw r3, #2928
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #2928
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	ldr lr, [r12, #3360]
	bx lr

vg_p384_point_double_umaal:
	mov r12, r0
	str lr, [r12, #3360]
	mov r0, r12
	movw r1, #3424
	movw r2, #2976
	movw r3, #2976
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3024
	movw r3, #3024
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3520
	movw r2, #3072
	movw r3, #3072
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3568
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3024
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3424
	movw r3, #3472
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3568
	movw r2, #3568
	movw r3, #3616
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #2976
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3664
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3664
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3024
	movw r3, #3072
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3664
	movw r2, #3664
	movw r3, #2832
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3264
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3312
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2832
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #2928
	movw r2, #3472
	movw r3, #2928
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #2880
	movw r2, #2832
	movw r3, #2928
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3424
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3312
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3472
	movw r2, #3472
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3424
	movw r3, #3520
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3520
	movw r2, #3264
	movw r3, #3520
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3616
	movw r3, #3520
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3472
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2880
	movw r2, #2880
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3664
	movw r3, #3616
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #3568
	movw r3, #2832
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2832
	movw r2, #2832
	movw r3, #3424
	bl {vg_p384_sub_mod_p}
	mov r0, r12
	movw r1, #3424
	movw r2, #3568
	movw r3, #3472
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #3664
	movw r3, #2928
	bl {vg_p384_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #2928
	movw r2, #2928
	movw r3, #3424
	bl {vg_p384_add_mod_p}
	ldr lr, [r12, #3360]
	bx lr
