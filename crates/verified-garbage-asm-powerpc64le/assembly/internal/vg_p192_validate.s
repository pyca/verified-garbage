// The functions of `src/internal/vg_p192_validate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_validate:
	std %r31, 1144(%r3)
	mflr %r0
	std %r0, 1152(%r3)
	li %r4, 880
	li %r5, 856
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 904
	li %r5, 928
	li %r6, 1000
	bl {vg_p192_mul_mod_p}
	li %r4, 952
	li %r5, 904
	li %r6, 904
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 880
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1072
	li %r5, 1048
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 1048
	li %r5, 208
	li %r6, 880
	bl {vg_p192_mul_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1048
	bl {vg_p192_add_mod_p}
	li %r4, 1072
	li %r5, 976
	li %r6, 1024
	bl {vg_p192_add_mod_p}
	li %r4, 1048
	li %r5, 952
	li %r6, 1072
	bl {vg_p192_sub_mod_p}
	ld %r5, 1048(%r3)
	ld %r4, 1056(%r3)
	or %r5, %r5, %r4
	ld %r4, 1064(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	li %r4, 0
	subf %r5, %r5, %r4
	addi %r5, %r5, -1
	ld %r4, 1120(%r3)
	and %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r10, 1120(%r3)
	ld %r4, 256(%r3)
	ld %r5, 880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 264(%r3)
	ld %r5, 888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 272(%r3)
	ld %r5, 896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 280(%r3)
	ld %r5, 904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1096(%r3)
	ld %r4, 288(%r3)
	ld %r5, 912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1104(%r3)
	ld %r4, 296(%r3)
	ld %r5, 920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1112(%r3)
	ld %r0, 1152(%r3)
	mtlr %r0
	ld %r31, 1144(%r3)
	blr
