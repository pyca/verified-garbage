// The functions of `src/internal/vg_p192_inv_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_inv_mod_p:
	mflr %r0
	std %r0, 1152(%r3)
	ld %r4, 448(%r3)
	std %r4, 472(%r3)
	ld %r4, 456(%r3)
	std %r4, 480(%r3)
	ld %r4, 464(%r3)
	std %r4, 488(%r3)
	li %r4, 664
	li %r5, 448
	li %r6, 448
	bl {vg_p192_mul_mod_p}
	li %r4, 496
	li %r5, 472
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 520
	li %r5, 496
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 544
	li %r5, 520
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 568
	li %r5, 544
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 592
	li %r5, 568
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 616
	li %r5, 592
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	li %r4, 640
	li %r5, 616
	li %r6, 664
	bl {vg_p192_mul_mod_p}
	ld %r4, 640(%r3)
	std %r4, 760(%r3)
	ld %r4, 648(%r3)
	std %r4, 768(%r3)
	ld %r4, 656(%r3)
	std %r4, 776(%r3)
	li %r31, 30
20:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 3
21:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 760
	li %r5, 760
	li %r6, 544
	bl {vg_p192_mul_mod_p}
	li %r31, 5
22:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_p}
	li %r31, 14
23:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	li %r4, 760
	li %r5, 760
	li %r6, 640
	bl {vg_p192_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 760
	li %r5, 760
	li %r6, 760
	bl {vg_p192_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 760
	li %r5, 760
	li %r6, 616
	bl {vg_p192_mul_mod_p}
	ld %r0, 1152(%r3)
	mtlr %r0
	blr
