// The functions of `src/internal/vg_p521_inv_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_inv_mod_p:
	mflr %r0
	std %r0, 3312(%r3)
	ld %r4, 1216(%r3)
	std %r4, 1288(%r3)
	ld %r4, 1224(%r3)
	std %r4, 1296(%r3)
	ld %r4, 1232(%r3)
	std %r4, 1304(%r3)
	ld %r4, 1240(%r3)
	std %r4, 1312(%r3)
	ld %r4, 1248(%r3)
	std %r4, 1320(%r3)
	ld %r4, 1256(%r3)
	std %r4, 1328(%r3)
	ld %r4, 1264(%r3)
	std %r4, 1336(%r3)
	ld %r4, 1272(%r3)
	std %r4, 1344(%r3)
	ld %r4, 1280(%r3)
	std %r4, 1352(%r3)
	li %r4, 1864
	li %r5, 1216
	li %r6, 1216
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1360
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 1432
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1576
	li %r5, 1504
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1648
	li %r5, 1576
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1720
	li %r5, 1648
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	ld %r4, 1792(%r3)
	std %r4, 2152(%r3)
	ld %r4, 1800(%r3)
	std %r4, 2160(%r3)
	ld %r4, 1808(%r3)
	std %r4, 2168(%r3)
	ld %r4, 1816(%r3)
	std %r4, 2176(%r3)
	ld %r4, 1824(%r3)
	std %r4, 2184(%r3)
	ld %r4, 1832(%r3)
	std %r4, 2192(%r3)
	ld %r4, 1840(%r3)
	std %r4, 2200(%r3)
	ld %r4, 1848(%r3)
	std %r4, 2208(%r3)
	ld %r4, 1856(%r3)
	std %r4, 2216(%r3)
	li %r31, 128
20:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2152
	li %r5, 2152
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 3
21:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r31, 2
22:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r4, 2152
	li %r5, 2152
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	ld %r0, 3312(%r3)
	mtlr %r0
	blr
