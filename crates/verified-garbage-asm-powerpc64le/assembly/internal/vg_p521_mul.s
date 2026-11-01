// The functions of `src/internal/vg_p521_mul.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul:
	std %r31, 3304(%r3)
	mflr %r0
	std %r0, 3312(%r3)
	li %r31, 72
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2296(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	ld %r4, 1072(%r3)
	std %r4, 2152(%r3)
	ld %r4, 1080(%r3)
	std %r4, 2160(%r3)
	ld %r4, 1088(%r3)
	std %r4, 2168(%r3)
	ld %r4, 1096(%r3)
	std %r4, 2176(%r3)
	ld %r4, 1104(%r3)
	std %r4, 2184(%r3)
	ld %r4, 1112(%r3)
	std %r4, 2192(%r3)
	ld %r4, 1120(%r3)
	std %r4, 2200(%r3)
	ld %r4, 1128(%r3)
	std %r4, 2208(%r3)
	ld %r4, 1136(%r3)
	std %r4, 2216(%r3)
	ld %r4, 1144(%r3)
	std %r4, 2224(%r3)
	ld %r4, 1152(%r3)
	std %r4, 2232(%r3)
	ld %r4, 1160(%r3)
	std %r4, 2240(%r3)
	ld %r4, 1168(%r3)
	std %r4, 2248(%r3)
	ld %r4, 1176(%r3)
	std %r4, 2256(%r3)
	ld %r4, 1184(%r3)
	std %r4, 2264(%r3)
	ld %r4, 1192(%r3)
	std %r4, 2272(%r3)
	ld %r4, 1200(%r3)
	std %r4, 2280(%r3)
	ld %r4, 1208(%r3)
	std %r4, 2288(%r3)
	ld %r4, 280(%r3)
	std %r4, 1072(%r3)
	ld %r4, 288(%r3)
	std %r4, 1080(%r3)
	ld %r4, 296(%r3)
	std %r4, 1088(%r3)
	ld %r4, 304(%r3)
	std %r4, 1096(%r3)
	ld %r4, 312(%r3)
	std %r4, 1104(%r3)
	ld %r4, 320(%r3)
	std %r4, 1112(%r3)
	ld %r4, 328(%r3)
	std %r4, 1120(%r3)
	ld %r4, 336(%r3)
	std %r4, 1128(%r3)
	ld %r4, 344(%r3)
	std %r4, 1136(%r3)
	ld %r4, 424(%r3)
	std %r4, 1144(%r3)
	ld %r4, 432(%r3)
	std %r4, 1152(%r3)
	ld %r4, 440(%r3)
	std %r4, 1160(%r3)
	ld %r4, 448(%r3)
	std %r4, 1168(%r3)
	ld %r4, 456(%r3)
	std %r4, 1176(%r3)
	ld %r4, 464(%r3)
	std %r4, 1184(%r3)
	ld %r4, 472(%r3)
	std %r4, 1192(%r3)
	ld %r4, 480(%r3)
	std %r4, 1200(%r3)
	ld %r4, 488(%r3)
	std %r4, 1208(%r3)
	ld %r4, 280(%r3)
	std %r4, 1216(%r3)
	ld %r4, 288(%r3)
	std %r4, 1224(%r3)
	ld %r4, 296(%r3)
	std %r4, 1232(%r3)
	ld %r4, 304(%r3)
	std %r4, 1240(%r3)
	ld %r4, 312(%r3)
	std %r4, 1248(%r3)
	ld %r4, 320(%r3)
	std %r4, 1256(%r3)
	ld %r4, 328(%r3)
	std %r4, 1264(%r3)
	ld %r4, 336(%r3)
	std %r4, 1272(%r3)
	ld %r4, 344(%r3)
	std %r4, 1280(%r3)
	li %r31, 528
21:
	addi %r31, %r31, -1
	li %r4, 1720
	li %r5, 1072
	li %r6, 1072
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1144
	li %r6, 1144
	bl {vg_p521_mul_mod_p}
	li %r4, 1864
	li %r5, 1216
	li %r6, 1216
	bl {vg_p521_mul_mod_p}
	li %r4, 1936
	li %r5, 1072
	li %r6, 1144
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 1072
	li %r6, 1144
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 1720
	li %r6, 1792
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_sub_mod_p}
	li %r4, 2008
	li %r5, 1072
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 1072
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_mul_mod_p}
	li %r4, 2080
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_sub_mod_p}
	li %r4, 2080
	li %r5, 1144
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1144
	li %r6, 1216
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1288
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 496
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 568
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1288
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_sub_mod_p}
	li %r4, 1432
	li %r5, 1792
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1360
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 568
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_sub_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1792
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 2080
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1936
	li %r6, 1288
	bl {vg_p521_mul_mod_p}
	li %r4, 1288
	li %r5, 1288
	li %r6, 1720
	bl {vg_p521_sub_mod_p}
	li %r4, 1720
	li %r5, 1936
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 2080
	li %r6, 1432
	bl {vg_p521_mul_mod_p}
	li %r4, 1432
	li %r5, 1432
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1288
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1360
	li %r6, 2224
	bl {vg_p521_mul_mod_p}
	li %r4, 1864
	li %r5, 1432
	li %r6, 424
	bl {vg_p521_mul_mod_p}
	li %r4, 1936
	li %r5, 1288
	li %r6, 1360
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2152
	li %r6, 2224
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 1720
	li %r6, 1792
	bl {vg_p521_add_mod_p}
	li %r4, 1936
	li %r5, 1936
	li %r6, 2008
	bl {vg_p521_sub_mod_p}
	li %r4, 2008
	li %r5, 1288
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2152
	li %r6, 424
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_mul_mod_p}
	li %r4, 2080
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 2080
	bl {vg_p521_sub_mod_p}
	li %r4, 2080
	li %r5, 1360
	li %r6, 1432
	bl {vg_p521_add_mod_p}
	li %r4, 1504
	li %r5, 2224
	li %r6, 424
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 2080
	li %r5, 2080
	li %r6, 1504
	bl {vg_p521_sub_mod_p}
	li %r4, 1648
	li %r5, 496
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 568
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 1648
	li %r5, 1504
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 1504
	li %r5, 1792
	li %r6, 1648
	bl {vg_p521_sub_mod_p}
	li %r4, 1648
	li %r5, 1792
	li %r6, 1648
	bl {vg_p521_add_mod_p}
	li %r4, 1576
	li %r5, 1504
	li %r6, 1648
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1720
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 568
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1864
	li %r5, 1720
	li %r6, 1864
	bl {vg_p521_sub_mod_p}
	li %r4, 1864
	li %r5, 496
	li %r6, 1864
	bl {vg_p521_mul_mod_p}
	li %r4, 2008
	li %r5, 2008
	li %r6, 1864
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 1792
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1576
	li %r5, 1576
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	li %r4, 1720
	li %r5, 2080
	li %r6, 2008
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 1936
	li %r6, 1504
	bl {vg_p521_mul_mod_p}
	li %r4, 1504
	li %r5, 1504
	li %r6, 1720
	bl {vg_p521_sub_mod_p}
	li %r4, 1720
	li %r5, 1936
	li %r6, 1792
	bl {vg_p521_mul_mod_p}
	li %r4, 1648
	li %r5, 2080
	li %r6, 1648
	bl {vg_p521_mul_mod_p}
	li %r4, 1648
	li %r5, 1648
	li %r6, 1720
	bl {vg_p521_add_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1288(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1072(%r3)
	ld %r4, 1296(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1080(%r3)
	ld %r4, 1304(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1088(%r3)
	ld %r4, 1312(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1096(%r3)
	ld %r4, 1320(%r3)
	ld %r5, 1536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1104(%r3)
	ld %r4, 1328(%r3)
	ld %r5, 1544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1112(%r3)
	ld %r4, 1336(%r3)
	ld %r5, 1552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r4, 1344(%r3)
	ld %r5, 1560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1128(%r3)
	ld %r4, 1352(%r3)
	ld %r5, 1568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1136(%r3)
	ld %r4, 1360(%r3)
	ld %r5, 1576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1144(%r3)
	ld %r4, 1368(%r3)
	ld %r5, 1584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1152(%r3)
	ld %r4, 1376(%r3)
	ld %r5, 1592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1160(%r3)
	ld %r4, 1384(%r3)
	ld %r5, 1600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1168(%r3)
	ld %r4, 1392(%r3)
	ld %r5, 1608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1176(%r3)
	ld %r4, 1400(%r3)
	ld %r5, 1616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1184(%r3)
	ld %r4, 1408(%r3)
	ld %r5, 1624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1192(%r3)
	ld %r4, 1416(%r3)
	ld %r5, 1632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1200(%r3)
	ld %r4, 1424(%r3)
	ld %r5, 1640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1208(%r3)
	ld %r4, 1432(%r3)
	ld %r5, 1648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1216(%r3)
	ld %r4, 1440(%r3)
	ld %r5, 1656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1224(%r3)
	ld %r4, 1448(%r3)
	ld %r5, 1664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1232(%r3)
	ld %r4, 1456(%r3)
	ld %r5, 1672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1240(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1248(%r3)
	ld %r4, 1472(%r3)
	ld %r5, 1688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1256(%r3)
	ld %r4, 1480(%r3)
	ld %r5, 1696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1264(%r3)
	ld %r4, 1488(%r3)
	ld %r5, 1704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1272(%r3)
	ld %r4, 1496(%r3)
	ld %r5, 1712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1280(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	ld %r0, 3312(%r3)
	mtlr %r0
	ld %r31, 3304(%r3)
	blr
