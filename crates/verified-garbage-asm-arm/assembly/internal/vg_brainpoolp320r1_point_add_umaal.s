// The functions of `src/internal/vg_brainpoolp320r1_point_add_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_point_add_umaal:
	mov r12, r0
	str lr, [r12, #3472]
	mov r0, r12
	movw r1, #3536
	movw r2, #3152
	movw r3, #3272
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3576
	movw r2, #3192
	movw r3, #3312
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3232
	movw r3, #3352
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3656
	movw r2, #3152
	movw r3, #3192
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3272
	movw r3, #3312
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3656
	movw r2, #3656
	movw r3, #3696
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3536
	movw r3, #3576
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3656
	movw r2, #3656
	movw r3, #3696
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3152
	movw r3, #3232
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3736
	movw r2, #3272
	movw r3, #3352
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3696
	movw r3, #3736
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3736
	movw r2, #3536
	movw r3, #3616
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3696
	movw r3, #3736
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3736
	movw r2, #3192
	movw r3, #3232
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3312
	movw r3, #3352
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3736
	movw r2, #3736
	movw r3, #3032
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3576
	movw r3, #3616
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3736
	movw r2, #3736
	movw r3, #3032
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3112
	movw r2, #3392
	movw r3, #3696
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3432
	movw r3, #3616
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3112
	movw r2, #3032
	movw r3, #3112
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3576
	movw r3, #3112
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3112
	movw r2, #3576
	movw r3, #3112
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3072
	movw r2, #3032
	movw r3, #3112
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3576
	movw r2, #3536
	movw r3, #3536
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3576
	movw r2, #3576
	movw r3, #3536
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3392
	movw r3, #3616
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3432
	movw r3, #3696
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3576
	movw r2, #3576
	movw r3, #3616
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3536
	movw r3, #3616
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3616
	movw r2, #3392
	movw r3, #3616
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3696
	movw r2, #3696
	movw r3, #3616
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3536
	movw r2, #3576
	movw r3, #3696
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3072
	movw r2, #3072
	movw r3, #3536
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	mov r0, r12
	movw r1, #3536
	movw r2, #3736
	movw r3, #3696
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3656
	movw r3, #3032
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3032
	movw r2, #3032
	movw r3, #3536
	bl {vg_brainpoolp320r1_sub_mod_p_umaal}
	mov r0, r12
	movw r1, #3536
	movw r2, #3656
	movw r3, #3576
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3112
	movw r2, #3736
	movw r3, #3112
	bl {vg_brainpoolp320r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3112
	movw r2, #3112
	movw r3, #3536
	bl {vg_brainpoolp320r1_add_mod_p_umaal}
	ldr lr, [r12, #3472]
	bx lr
