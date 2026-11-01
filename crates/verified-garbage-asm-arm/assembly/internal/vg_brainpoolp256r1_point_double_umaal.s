// The functions of `src/internal/vg_brainpoolp256r1_point_double_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_point_double_umaal:
	mov r12, r0
	str lr, [r12, #3584]
	mov r0, r12
	movw r1, #3648
	movw r2, #3328
	movw r3, #3328
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3680
	movw r2, #3360
	movw r3, #3360
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3712
	movw r2, #3392
	movw r3, #3392
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3744
	movw r2, #3328
	movw r3, #3360
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3776
	movw r2, #3328
	movw r3, #3360
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3744
	movw r2, #3744
	movw r3, #3776
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3776
	movw r2, #3648
	movw r3, #3680
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3744
	movw r2, #3744
	movw r3, #3776
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3776
	movw r2, #3328
	movw r3, #3392
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3328
	movw r3, #3392
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3776
	movw r2, #3776
	movw r3, #3808
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3808
	movw r2, #3648
	movw r3, #3712
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3776
	movw r2, #3776
	movw r3, #3808
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3360
	movw r3, #3392
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3232
	movw r2, #3360
	movw r3, #3392
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3808
	movw r3, #3232
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3232
	movw r2, #3680
	movw r3, #3712
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3808
	movw r3, #3232
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3296
	movw r2, #3520
	movw r3, #3776
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3232
	movw r2, #3552
	movw r3, #3712
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3296
	movw r2, #3232
	movw r3, #3296
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3232
	movw r2, #3680
	movw r3, #3296
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3296
	movw r2, #3680
	movw r3, #3296
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3264
	movw r2, #3232
	movw r3, #3296
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3680
	movw r2, #3648
	movw r3, #3648
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3680
	movw r2, #3680
	movw r3, #3648
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3712
	movw r2, #3520
	movw r3, #3712
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3776
	movw r2, #3552
	movw r3, #3776
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3680
	movw r2, #3680
	movw r3, #3712
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3712
	movw r2, #3648
	movw r3, #3712
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3712
	movw r2, #3520
	movw r3, #3712
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3776
	movw r2, #3776
	movw r3, #3712
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3648
	movw r2, #3680
	movw r3, #3776
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3264
	movw r2, #3264
	movw r3, #3648
	bl {vg_brainpoolp256r1_add_mod_p}
	mov r0, r12
	movw r1, #3648
	movw r2, #3808
	movw r3, #3776
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3232
	movw r2, #3744
	movw r3, #3232
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3232
	movw r2, #3232
	movw r3, #3648
	bl {vg_brainpoolp256r1_sub_mod_p}
	mov r0, r12
	movw r1, #3648
	movw r2, #3744
	movw r3, #3680
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3296
	movw r2, #3808
	movw r3, #3296
	bl {vg_brainpoolp256r1_mul_mod_p_umaal}
	mov r0, r12
	movw r1, #3296
	movw r2, #3296
	movw r3, #3648
	bl {vg_brainpoolp256r1_add_mod_p}
	ldr lr, [r12, #3584]
	bx lr
