// The functions of `src/internal/vg_p192_point_add.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_point_add:
	mov r12, r0
	str lr, [r12, #3696]
	mov r0, r12
	movw r1, #3760
	movw r2, #3504
	movw r3, #3576
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3784
	movw r2, #3528
	movw r3, #3600
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3552
	movw r3, #3624
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3832
	movw r2, #3504
	movw r3, #3528
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3576
	movw r3, #3600
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3832
	movw r2, #3832
	movw r3, #3856
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3760
	movw r3, #3784
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3832
	movw r2, #3832
	movw r3, #3856
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3504
	movw r3, #3552
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3880
	movw r2, #3576
	movw r3, #3624
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3856
	movw r3, #3880
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3880
	movw r2, #3760
	movw r3, #3808
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3856
	movw r3, #3880
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3880
	movw r2, #3528
	movw r3, #3552
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3600
	movw r3, #3624
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3880
	movw r2, #3880
	movw r3, #3432
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3784
	movw r3, #3808
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3880
	movw r2, #3880
	movw r3, #3432
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3480
	movw r2, #3648
	movw r3, #3856
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3672
	movw r3, #3808
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3480
	movw r2, #3432
	movw r3, #3480
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3784
	movw r3, #3480
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3480
	movw r2, #3784
	movw r3, #3480
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3456
	movw r2, #3432
	movw r3, #3480
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3784
	movw r2, #3760
	movw r3, #3760
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3784
	movw r2, #3784
	movw r3, #3760
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3648
	movw r3, #3808
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3672
	movw r3, #3856
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3784
	movw r2, #3784
	movw r3, #3808
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3760
	movw r3, #3808
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3808
	movw r2, #3648
	movw r3, #3808
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3856
	movw r2, #3856
	movw r3, #3808
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3760
	movw r2, #3784
	movw r3, #3856
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3456
	movw r2, #3456
	movw r3, #3760
	bl {vg_p192_add_mod_p}
	mov r0, r12
	movw r1, #3760
	movw r2, #3880
	movw r3, #3856
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3832
	movw r3, #3432
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3432
	movw r2, #3432
	movw r3, #3760
	bl {vg_p192_sub_mod_p}
	mov r0, r12
	movw r1, #3760
	movw r2, #3832
	movw r3, #3784
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3480
	movw r2, #3880
	movw r3, #3480
	bl {vg_p192_mul_mod_p}
	mov r0, r12
	movw r1, #3480
	movw r2, #3480
	movw r3, #3760
	bl {vg_p192_add_mod_p}
	ldr lr, [r12, #3696]
	bx lr
