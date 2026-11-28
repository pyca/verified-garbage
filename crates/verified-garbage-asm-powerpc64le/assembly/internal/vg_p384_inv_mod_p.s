// The functions of `src/internal/vg_p384_inv_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_inv_mod_p:
	mflr %r0
	std %r0, 2232(%r3)
	ld %r4, 832(%r3)
	std %r4, 880(%r3)
	ld %r4, 840(%r3)
	std %r4, 888(%r3)
	ld %r4, 848(%r3)
	std %r4, 896(%r3)
	ld %r4, 856(%r3)
	std %r4, 904(%r3)
	ld %r4, 864(%r3)
	std %r4, 912(%r3)
	ld %r4, 872(%r3)
	std %r4, 920(%r3)
	li %r4, 1264
	li %r5, 832
	li %r6, 832
	bl {vg_p384_mul_mod_p}
	li %r4, 928
	li %r5, 880
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 928
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 976
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1168
	li %r5, 1120
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	ld %r4, 1216(%r3)
	std %r4, 1456(%r3)
	ld %r4, 1224(%r3)
	std %r4, 1464(%r3)
	ld %r4, 1232(%r3)
	std %r4, 1472(%r3)
	ld %r4, 1240(%r3)
	std %r4, 1480(%r3)
	ld %r4, 1248(%r3)
	std %r4, 1488(%r3)
	ld %r4, 1256(%r3)
	std %r4, 1496(%r3)
	li %r31, 62
20:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 3
21:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r31, 5
22:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r31, 7
23:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	li %r31, 68
24:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r31, 6
25:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_p384_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	ld %r0, 2232(%r3)
	mtlr %r0
	blr
