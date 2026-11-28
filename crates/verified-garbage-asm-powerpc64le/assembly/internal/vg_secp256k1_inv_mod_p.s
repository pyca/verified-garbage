// The functions of `src/internal/vg_secp256k1_inv_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_inv_mod_p:
	mflr %r0
	std %r0, 1512(%r3)
	ld %r4, 576(%r3)
	std %r4, 608(%r3)
	ld %r4, 584(%r3)
	std %r4, 616(%r3)
	ld %r4, 592(%r3)
	std %r4, 624(%r3)
	ld %r4, 600(%r3)
	std %r4, 632(%r3)
	li %r4, 864
	li %r5, 576
	li %r6, 576
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 640
	li %r5, 608
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 672
	li %r5, 640
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 704
	li %r5, 672
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 736
	li %r5, 704
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 768
	li %r5, 736
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 800
	li %r5, 768
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 832
	li %r5, 800
	li %r6, 864
	bl {vg_secp256k1_mul_mod_p}
	ld %r4, 832(%r3)
	std %r4, 992(%r3)
	ld %r4, 840(%r3)
	std %r4, 1000(%r3)
	ld %r4, 848(%r3)
	std %r4, 1008(%r3)
	ld %r4, 856(%r3)
	std %r4, 1016(%r3)
	li %r31, 54
20:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 3
21:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 992
	li %r5, 992
	li %r6, 704
	bl {vg_secp256k1_mul_mod_p}
	li %r31, 5
22:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_secp256k1_mul_mod_p}
	li %r31, 4
23:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	li %r4, 992
	li %r5, 992
	li %r6, 832
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r31, 2
24:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 992
	li %r5, 992
	li %r6, 640
	bl {vg_secp256k1_mul_mod_p}
	li %r31, 8
25:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 992
	li %r5, 992
	li %r6, 768
	bl {vg_secp256k1_mul_mod_p}
	li %r31, 2
26:
	addi %r31, %r31, -1
	li %r4, 992
	li %r5, 992
	li %r6, 992
	bl {vg_secp256k1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 992
	li %r5, 992
	li %r6, 608
	bl {vg_secp256k1_mul_mod_p}
	ld %r0, 1512(%r3)
	mtlr %r0
	blr
