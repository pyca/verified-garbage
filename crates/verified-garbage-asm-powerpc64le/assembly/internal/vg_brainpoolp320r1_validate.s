// The functions of `src/internal/vg_brainpoolp320r1_validate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_validate:
	std %r31, 1864(%r3)
	mflr %r0
	std %r0, 1872(%r3)
	li %r4, 1424
	li %r5, 1384
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1464
	li %r5, 1504
	li %r6, 1624
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1544
	li %r5, 1464
	li %r6, 1464
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1704
	li %r5, 1424
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1704
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1704
	li %r5, 304
	li %r6, 1424
	bl {vg_brainpoolp320r1_mul_mod_p}
	li %r4, 1584
	li %r5, 1744
	li %r6, 1704
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1744
	li %r5, 1584
	li %r6, 1664
	bl {vg_brainpoolp320r1_add_mod_p}
	li %r4, 1704
	li %r5, 1544
	li %r6, 1744
	bl {vg_brainpoolp320r1_sub_mod_p}
	ld %r5, 1704(%r3)
	ld %r4, 1712(%r3)
	or %r5, %r5, %r4
	ld %r4, 1720(%r3)
	or %r5, %r5, %r4
	ld %r4, 1728(%r3)
	or %r5, %r5, %r4
	ld %r4, 1736(%r3)
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
	ld %r4, 1824(%r3)
	and %r4, %r4, %r5
	std %r4, 1824(%r3)
	ld %r10, 1824(%r3)
	ld %r4, 384(%r3)
	ld %r5, 1424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1584(%r3)
	ld %r4, 392(%r3)
	ld %r5, 1432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1592(%r3)
	ld %r4, 400(%r3)
	ld %r5, 1440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1600(%r3)
	ld %r4, 408(%r3)
	ld %r5, 1448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1608(%r3)
	ld %r4, 416(%r3)
	ld %r5, 1456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1616(%r3)
	ld %r4, 424(%r3)
	ld %r5, 1464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1784(%r3)
	ld %r4, 432(%r3)
	ld %r5, 1472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1792(%r3)
	ld %r4, 440(%r3)
	ld %r5, 1480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1800(%r3)
	ld %r4, 448(%r3)
	ld %r5, 1488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1808(%r3)
	ld %r4, 456(%r3)
	ld %r5, 1496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1816(%r3)
	ld %r0, 1872(%r3)
	mtlr %r0
	ld %r31, 1864(%r3)
	blr
