// The functions of `src/sm4.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key:
	stdu %r1, -3248(%r1)
	addi %r5, %r1, 32
	or %r8, %r5, %r5
	std %r14, 3072(%r8)
	std %r15, 3080(%r8)
	std %r16, 3088(%r8)
	std %r17, 3096(%r8)
	std %r18, 3104(%r8)
	std %r19, 3112(%r8)
	std %r20, 3120(%r8)
	std %r21, 3128(%r8)
	std %r22, 3136(%r8)
	std %r23, 3144(%r8)
	std %r24, 3152(%r8)
	std %r25, 3160(%r8)
	std %r26, 3168(%r8)
	std %r27, 3176(%r8)
	std %r28, 3184(%r8)
	std %r29, 3192(%r8)
	std %r30, 3200(%r8)
	std %r31, 3208(%r8)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 255
	std %r22, 384(%r8)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65280
	std %r22, 392(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 400(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1024(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1032(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1040(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1048(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1056(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1064(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1072(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1080(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1088(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1096(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1104(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1112(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1120(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1128(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1136(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1144(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1152(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1160(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1168(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1176(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1184(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1192(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1200(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1208(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1216(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1224(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1232(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1240(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1248(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1256(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1264(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1272(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1280(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1288(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1296(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1304(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1312(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1320(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1328(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1336(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1344(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1352(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1360(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1368(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1376(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1384(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1392(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1400(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1408(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1416(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1424(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1432(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1440(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1448(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1456(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1464(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1472(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1480(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1488(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1496(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1504(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1512(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1520(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1528(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1536(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1544(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1552(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1560(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1568(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1576(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1584(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1592(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1600(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1608(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1616(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1624(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1632(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1640(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1648(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1656(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1664(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1672(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1680(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1688(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1696(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1704(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1712(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1720(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1728(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1736(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1744(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1752(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1760(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1768(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1776(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1784(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1792(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1800(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1808(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1816(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1824(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1832(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1840(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1848(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1856(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1864(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1872(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 1880(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1888(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1896(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1904(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1912(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1920(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1928(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1936(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1944(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1952(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1960(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 1968(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 1976(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1984(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 1992(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2000(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2008(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2016(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2024(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2032(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2040(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2048(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2056(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2064(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2072(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2080(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2088(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2096(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2104(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2112(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2120(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2128(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2136(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2144(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2152(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2160(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2168(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2176(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2184(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2192(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2200(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2208(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2216(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2224(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2232(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2240(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2248(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2256(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2264(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2272(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2280(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2288(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2296(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2304(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2312(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2320(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2328(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2336(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2344(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2352(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2360(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2368(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2376(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2384(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2392(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2400(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2408(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2416(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2424(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2432(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2440(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2448(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2456(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2464(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2472(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2480(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2488(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2496(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2504(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2512(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2520(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2528(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2536(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2544(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2552(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2560(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2568(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2576(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2584(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2592(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2600(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2608(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2616(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2624(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2632(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2640(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2648(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2656(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2664(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2672(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2680(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2688(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2696(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2704(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2712(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2720(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2728(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2736(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2744(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2752(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2760(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2768(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2776(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2784(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2792(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2800(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2808(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2816(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2824(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2832(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2840(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2848(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2856(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2864(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2872(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2880(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2888(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2896(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 2904(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2912(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2920(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2928(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2936(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2944(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2952(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 2960(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2968(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2976(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 2984(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 2992(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 3000(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 3008(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 3016(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 3024(%r8)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 3032(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 3040(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 3048(%r8)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 3056(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 3064(%r8)
	ld %r22, 0(%r3)
	lis %r23, 20531
	ori %r23, %r23, 43606
	rldicr %r23, %r23, 32, 31
	oris %r23, %r23, 50874
	ori %r23, %r23, 45475
	xor %r22, %r22, %r23
	std %r22, 768(%r8)
	std %r22, 784(%r8)
	std %r22, 800(%r8)
	std %r22, 816(%r8)
	std %r22, 832(%r8)
	std %r22, 848(%r8)
	std %r22, 864(%r8)
	std %r22, 880(%r8)
	std %r22, 896(%r8)
	std %r22, 912(%r8)
	std %r22, 928(%r8)
	std %r22, 944(%r8)
	std %r22, 960(%r8)
	std %r22, 976(%r8)
	std %r22, 992(%r8)
	std %r22, 1008(%r8)
	ld %r22, 8(%r3)
	lis %r23, -9182
	ori %r23, %r23, 28850
	rldicr %r23, %r23, 32, 31
	oris %r23, %r23, 38801
	ori %r23, %r23, 32103
	xor %r22, %r22, %r23
	std %r22, 776(%r8)
	std %r22, 792(%r8)
	std %r22, 808(%r8)
	std %r22, 824(%r8)
	std %r22, 840(%r8)
	std %r22, 856(%r8)
	std %r22, 872(%r8)
	std %r22, 888(%r8)
	std %r22, 904(%r8)
	std %r22, 920(%r8)
	std %r22, 936(%r8)
	std %r22, 952(%r8)
	std %r22, 968(%r8)
	std %r22, 984(%r8)
	std %r22, 1000(%r8)
	std %r22, 1016(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r26, 255
	ori %r26, %r26, 255
	rldicr %r26, %r26, 32, 31
	oris %r26, %r26, 255
	ori %r26, %r26, 255
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	ld %r14, 768(%r8)
	ld %r18, 896(%r8)
	ld %r15, 784(%r8)
	ld %r19, 912(%r8)
	ld %r16, 800(%r8)
	ld %r20, 928(%r8)
	ld %r17, 816(%r8)
	ld %r21, 944(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 768(%r8)
	std %r18, 896(%r8)
	std %r15, 784(%r8)
	std %r19, 912(%r8)
	std %r16, 800(%r8)
	std %r20, 928(%r8)
	std %r17, 816(%r8)
	std %r21, 944(%r8)
	ld %r14, 832(%r8)
	ld %r18, 960(%r8)
	ld %r15, 848(%r8)
	ld %r19, 976(%r8)
	ld %r16, 864(%r8)
	ld %r20, 992(%r8)
	ld %r17, 880(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 832(%r8)
	std %r18, 960(%r8)
	std %r15, 848(%r8)
	std %r19, 976(%r8)
	std %r16, 864(%r8)
	std %r20, 992(%r8)
	std %r17, 880(%r8)
	std %r21, 1008(%r8)
	ld %r14, 776(%r8)
	ld %r18, 904(%r8)
	ld %r15, 792(%r8)
	ld %r19, 920(%r8)
	ld %r16, 808(%r8)
	ld %r20, 936(%r8)
	ld %r17, 824(%r8)
	ld %r21, 952(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 776(%r8)
	std %r18, 904(%r8)
	std %r15, 792(%r8)
	std %r19, 920(%r8)
	std %r16, 808(%r8)
	std %r20, 936(%r8)
	std %r17, 824(%r8)
	std %r21, 952(%r8)
	ld %r14, 840(%r8)
	ld %r18, 968(%r8)
	ld %r15, 856(%r8)
	ld %r19, 984(%r8)
	ld %r16, 872(%r8)
	ld %r20, 1000(%r8)
	ld %r17, 888(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 840(%r8)
	std %r18, 968(%r8)
	std %r15, 856(%r8)
	std %r19, 984(%r8)
	std %r16, 872(%r8)
	std %r20, 1000(%r8)
	std %r17, 888(%r8)
	std %r21, 1016(%r8)
	ld %r14, 768(%r8)
	ld %r15, 784(%r8)
	ld %r16, 800(%r8)
	ld %r17, 816(%r8)
	ld %r18, 832(%r8)
	ld %r19, 848(%r8)
	ld %r20, 864(%r8)
	ld %r21, 880(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	ld %r14, 896(%r8)
	ld %r15, 912(%r8)
	ld %r16, 928(%r8)
	ld %r17, 944(%r8)
	ld %r18, 960(%r8)
	ld %r19, 976(%r8)
	ld %r20, 992(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 776(%r8)
	ld %r15, 792(%r8)
	ld %r16, 808(%r8)
	ld %r17, 824(%r8)
	ld %r18, 840(%r8)
	ld %r19, 856(%r8)
	ld %r20, 872(%r8)
	ld %r21, 888(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 640(%r8)
	std %r15, 648(%r8)
	std %r16, 656(%r8)
	std %r17, 664(%r8)
	std %r18, 672(%r8)
	std %r19, 680(%r8)
	std %r20, 688(%r8)
	std %r21, 696(%r8)
	ld %r14, 904(%r8)
	ld %r15, 920(%r8)
	ld %r16, 936(%r8)
	ld %r17, 952(%r8)
	ld %r18, 968(%r8)
	ld %r19, 984(%r8)
	ld %r20, 1000(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 704(%r8)
	std %r15, 712(%r8)
	std %r16, 720(%r8)
	std %r17, 728(%r8)
	std %r18, 736(%r8)
	std %r19, 744(%r8)
	std %r20, 752(%r8)
	std %r21, 760(%r8)
	addi %r11, %r8, 3072
	addi %r10, %r8, 1024
20:
	ld %r14, 576(%r8)
	ld %r22, 640(%r8)
	xor %r14, %r14, %r22
	ld %r22, 704(%r8)
	xor %r14, %r14, %r22
	ld %r22, 0(%r10)
	xor %r14, %r14, %r22
	ld %r15, 584(%r8)
	ld %r22, 648(%r8)
	xor %r15, %r15, %r22
	ld %r22, 712(%r8)
	xor %r15, %r15, %r22
	ld %r22, 8(%r10)
	xor %r15, %r15, %r22
	ld %r16, 592(%r8)
	ld %r22, 656(%r8)
	xor %r16, %r16, %r22
	ld %r22, 720(%r8)
	xor %r16, %r16, %r22
	ld %r22, 16(%r10)
	xor %r16, %r16, %r22
	ld %r17, 600(%r8)
	ld %r22, 664(%r8)
	xor %r17, %r17, %r22
	ld %r22, 728(%r8)
	xor %r17, %r17, %r22
	ld %r22, 24(%r10)
	xor %r17, %r17, %r22
	ld %r18, 608(%r8)
	ld %r22, 672(%r8)
	xor %r18, %r18, %r22
	ld %r22, 736(%r8)
	xor %r18, %r18, %r22
	ld %r22, 32(%r10)
	xor %r18, %r18, %r22
	ld %r19, 616(%r8)
	ld %r22, 680(%r8)
	xor %r19, %r19, %r22
	ld %r22, 744(%r8)
	xor %r19, %r19, %r22
	ld %r22, 40(%r10)
	xor %r19, %r19, %r22
	ld %r20, 624(%r8)
	ld %r22, 688(%r8)
	xor %r20, %r20, %r22
	ld %r22, 752(%r8)
	xor %r20, %r20, %r22
	ld %r22, 48(%r10)
	xor %r20, %r20, %r22
	ld %r21, 632(%r8)
	ld %r22, 696(%r8)
	xor %r21, %r21, %r22
	ld %r22, 760(%r8)
	xor %r21, %r21, %r22
	ld %r22, 56(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r22, %r17, 32, 0
	xor %r22, %r22, %r14
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 512(%r8)
	xor %r22, %r22, %r23
	std %r22, 512(%r8)
	rldicl %r22, %r18, 32, 0
	xor %r22, %r22, %r15
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 520(%r8)
	xor %r22, %r22, %r23
	std %r22, 520(%r8)
	rldicl %r22, %r19, 32, 0
	xor %r22, %r22, %r16
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 528(%r8)
	xor %r22, %r22, %r23
	std %r22, 528(%r8)
	rldicl %r22, %r20, 32, 0
	xor %r22, %r22, %r17
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 536(%r8)
	xor %r22, %r22, %r23
	std %r22, 536(%r8)
	rldicl %r22, %r21, 32, 0
	xor %r22, %r22, %r18
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 544(%r8)
	xor %r22, %r22, %r23
	std %r22, 544(%r8)
	rldicl %r22, %r14, 48, 0
	xor %r22, %r22, %r19
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 552(%r8)
	xor %r22, %r22, %r23
	std %r22, 552(%r8)
	rldicl %r22, %r15, 48, 0
	xor %r22, %r22, %r20
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 560(%r8)
	xor %r22, %r22, %r23
	std %r22, 560(%r8)
	rldicl %r22, %r16, 48, 0
	xor %r22, %r22, %r21
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	ld %r23, 568(%r8)
	xor %r22, %r22, %r23
	std %r22, 568(%r8)
	ld %r14, 640(%r8)
	ld %r22, 704(%r8)
	xor %r14, %r14, %r22
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	ld %r22, 64(%r10)
	xor %r14, %r14, %r22
	ld %r15, 648(%r8)
	ld %r22, 712(%r8)
	xor %r15, %r15, %r22
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	ld %r22, 72(%r10)
	xor %r15, %r15, %r22
	ld %r16, 656(%r8)
	ld %r22, 720(%r8)
	xor %r16, %r16, %r22
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	ld %r22, 80(%r10)
	xor %r16, %r16, %r22
	ld %r17, 664(%r8)
	ld %r22, 728(%r8)
	xor %r17, %r17, %r22
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	ld %r22, 88(%r10)
	xor %r17, %r17, %r22
	ld %r18, 672(%r8)
	ld %r22, 736(%r8)
	xor %r18, %r18, %r22
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	ld %r22, 96(%r10)
	xor %r18, %r18, %r22
	ld %r19, 680(%r8)
	ld %r22, 744(%r8)
	xor %r19, %r19, %r22
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	ld %r22, 104(%r10)
	xor %r19, %r19, %r22
	ld %r20, 688(%r8)
	ld %r22, 752(%r8)
	xor %r20, %r20, %r22
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	ld %r22, 112(%r10)
	xor %r20, %r20, %r22
	ld %r21, 696(%r8)
	ld %r22, 760(%r8)
	xor %r21, %r21, %r22
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	ld %r22, 120(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r22, %r17, 32, 0
	xor %r22, %r22, %r14
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 576(%r8)
	xor %r22, %r22, %r23
	std %r22, 576(%r8)
	rldicl %r22, %r18, 32, 0
	xor %r22, %r22, %r15
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 584(%r8)
	xor %r22, %r22, %r23
	std %r22, 584(%r8)
	rldicl %r22, %r19, 32, 0
	xor %r22, %r22, %r16
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 592(%r8)
	xor %r22, %r22, %r23
	std %r22, 592(%r8)
	rldicl %r22, %r20, 32, 0
	xor %r22, %r22, %r17
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 600(%r8)
	xor %r22, %r22, %r23
	std %r22, 600(%r8)
	rldicl %r22, %r21, 32, 0
	xor %r22, %r22, %r18
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 608(%r8)
	xor %r22, %r22, %r23
	std %r22, 608(%r8)
	rldicl %r22, %r14, 48, 0
	xor %r22, %r22, %r19
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 616(%r8)
	xor %r22, %r22, %r23
	std %r22, 616(%r8)
	rldicl %r22, %r15, 48, 0
	xor %r22, %r22, %r20
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 624(%r8)
	xor %r22, %r22, %r23
	std %r22, 624(%r8)
	rldicl %r22, %r16, 48, 0
	xor %r22, %r22, %r21
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	ld %r23, 632(%r8)
	xor %r22, %r22, %r23
	std %r22, 632(%r8)
	ld %r14, 704(%r8)
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	ld %r22, 128(%r10)
	xor %r14, %r14, %r22
	ld %r15, 712(%r8)
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	ld %r22, 136(%r10)
	xor %r15, %r15, %r22
	ld %r16, 720(%r8)
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	ld %r22, 144(%r10)
	xor %r16, %r16, %r22
	ld %r17, 728(%r8)
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	ld %r22, 152(%r10)
	xor %r17, %r17, %r22
	ld %r18, 736(%r8)
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	ld %r22, 160(%r10)
	xor %r18, %r18, %r22
	ld %r19, 744(%r8)
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	ld %r22, 168(%r10)
	xor %r19, %r19, %r22
	ld %r20, 752(%r8)
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	ld %r22, 176(%r10)
	xor %r20, %r20, %r22
	ld %r21, 760(%r8)
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	ld %r22, 184(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r22, %r17, 32, 0
	xor %r22, %r22, %r14
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 640(%r8)
	xor %r22, %r22, %r23
	std %r22, 640(%r8)
	rldicl %r22, %r18, 32, 0
	xor %r22, %r22, %r15
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 648(%r8)
	xor %r22, %r22, %r23
	std %r22, 648(%r8)
	rldicl %r22, %r19, 32, 0
	xor %r22, %r22, %r16
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 656(%r8)
	xor %r22, %r22, %r23
	std %r22, 656(%r8)
	rldicl %r22, %r20, 32, 0
	xor %r22, %r22, %r17
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 664(%r8)
	xor %r22, %r22, %r23
	std %r22, 664(%r8)
	rldicl %r22, %r21, 32, 0
	xor %r22, %r22, %r18
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 672(%r8)
	xor %r22, %r22, %r23
	std %r22, 672(%r8)
	rldicl %r22, %r14, 48, 0
	xor %r22, %r22, %r19
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 680(%r8)
	xor %r22, %r22, %r23
	std %r22, 680(%r8)
	rldicl %r22, %r15, 48, 0
	xor %r22, %r22, %r20
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 688(%r8)
	xor %r22, %r22, %r23
	std %r22, 688(%r8)
	rldicl %r22, %r16, 48, 0
	xor %r22, %r22, %r21
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	ld %r23, 696(%r8)
	xor %r22, %r22, %r23
	std %r22, 696(%r8)
	ld %r14, 512(%r8)
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	ld %r22, 640(%r8)
	xor %r14, %r14, %r22
	ld %r22, 192(%r10)
	xor %r14, %r14, %r22
	ld %r15, 520(%r8)
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	ld %r22, 648(%r8)
	xor %r15, %r15, %r22
	ld %r22, 200(%r10)
	xor %r15, %r15, %r22
	ld %r16, 528(%r8)
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	ld %r22, 656(%r8)
	xor %r16, %r16, %r22
	ld %r22, 208(%r10)
	xor %r16, %r16, %r22
	ld %r17, 536(%r8)
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	ld %r22, 664(%r8)
	xor %r17, %r17, %r22
	ld %r22, 216(%r10)
	xor %r17, %r17, %r22
	ld %r18, 544(%r8)
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	ld %r22, 672(%r8)
	xor %r18, %r18, %r22
	ld %r22, 224(%r10)
	xor %r18, %r18, %r22
	ld %r19, 552(%r8)
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	ld %r22, 680(%r8)
	xor %r19, %r19, %r22
	ld %r22, 232(%r10)
	xor %r19, %r19, %r22
	ld %r20, 560(%r8)
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	ld %r22, 688(%r8)
	xor %r20, %r20, %r22
	ld %r22, 240(%r10)
	xor %r20, %r20, %r22
	ld %r21, 568(%r8)
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	ld %r22, 696(%r8)
	xor %r21, %r21, %r22
	ld %r22, 248(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r22, %r17, 32, 0
	xor %r22, %r22, %r14
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 704(%r8)
	xor %r22, %r22, %r23
	std %r22, 704(%r8)
	rldicl %r22, %r18, 32, 0
	xor %r22, %r22, %r15
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 712(%r8)
	xor %r22, %r22, %r23
	std %r22, 712(%r8)
	rldicl %r22, %r19, 32, 0
	xor %r22, %r22, %r16
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 720(%r8)
	xor %r22, %r22, %r23
	std %r22, 720(%r8)
	rldicl %r22, %r20, 32, 0
	xor %r22, %r22, %r17
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 728(%r8)
	xor %r22, %r22, %r23
	std %r22, 728(%r8)
	rldicl %r22, %r21, 32, 0
	xor %r22, %r22, %r18
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 736(%r8)
	xor %r22, %r22, %r23
	std %r22, 736(%r8)
	rldicl %r22, %r14, 48, 0
	xor %r22, %r22, %r19
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 744(%r8)
	xor %r22, %r22, %r23
	std %r22, 744(%r8)
	rldicl %r22, %r15, 48, 0
	xor %r22, %r22, %r20
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 752(%r8)
	xor %r22, %r22, %r23
	std %r22, 752(%r8)
	rldicl %r22, %r16, 48, 0
	xor %r22, %r22, %r21
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	ld %r23, 760(%r8)
	xor %r22, %r22, %r23
	std %r22, 760(%r8)
	addi %r10, %r10, 256
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r26, 255
	ori %r26, %r26, 255
	rldicr %r26, %r26, 32, 31
	oris %r26, %r26, 255
	ori %r26, %r26, 255
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	ld %r14, 704(%r8)
	ld %r15, 712(%r8)
	ld %r16, 720(%r8)
	ld %r17, 728(%r8)
	ld %r18, 736(%r8)
	ld %r19, 744(%r8)
	ld %r20, 752(%r8)
	ld %r21, 760(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 768(%r8)
	std %r15, 784(%r8)
	std %r16, 800(%r8)
	std %r17, 816(%r8)
	std %r18, 832(%r8)
	std %r19, 848(%r8)
	std %r20, 864(%r8)
	std %r21, 880(%r8)
	ld %r14, 640(%r8)
	ld %r15, 648(%r8)
	ld %r16, 656(%r8)
	ld %r17, 664(%r8)
	ld %r18, 672(%r8)
	ld %r19, 680(%r8)
	ld %r20, 688(%r8)
	ld %r21, 696(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 896(%r8)
	std %r15, 912(%r8)
	std %r16, 928(%r8)
	std %r17, 944(%r8)
	std %r18, 960(%r8)
	std %r19, 976(%r8)
	std %r20, 992(%r8)
	std %r21, 1008(%r8)
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 776(%r8)
	std %r15, 792(%r8)
	std %r16, 808(%r8)
	std %r17, 824(%r8)
	std %r18, 840(%r8)
	std %r19, 856(%r8)
	std %r20, 872(%r8)
	std %r21, 888(%r8)
	ld %r14, 512(%r8)
	ld %r15, 520(%r8)
	ld %r16, 528(%r8)
	ld %r17, 536(%r8)
	ld %r18, 544(%r8)
	ld %r19, 552(%r8)
	ld %r20, 560(%r8)
	ld %r21, 568(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 904(%r8)
	std %r15, 920(%r8)
	std %r16, 936(%r8)
	std %r17, 952(%r8)
	std %r18, 968(%r8)
	std %r19, 984(%r8)
	std %r20, 1000(%r8)
	std %r21, 1016(%r8)
	ld %r14, 768(%r8)
	ld %r18, 896(%r8)
	ld %r15, 784(%r8)
	ld %r19, 912(%r8)
	ld %r16, 800(%r8)
	ld %r20, 928(%r8)
	ld %r17, 816(%r8)
	ld %r21, 944(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 768(%r8)
	std %r18, 896(%r8)
	std %r15, 784(%r8)
	std %r19, 912(%r8)
	std %r16, 800(%r8)
	std %r20, 928(%r8)
	std %r17, 816(%r8)
	std %r21, 944(%r8)
	ld %r14, 832(%r8)
	ld %r18, 960(%r8)
	ld %r15, 848(%r8)
	ld %r19, 976(%r8)
	ld %r16, 864(%r8)
	ld %r20, 992(%r8)
	ld %r17, 880(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 832(%r8)
	std %r18, 960(%r8)
	std %r15, 848(%r8)
	std %r19, 976(%r8)
	std %r16, 864(%r8)
	std %r20, 992(%r8)
	std %r17, 880(%r8)
	std %r21, 1008(%r8)
	ld %r14, 776(%r8)
	ld %r18, 904(%r8)
	ld %r15, 792(%r8)
	ld %r19, 920(%r8)
	ld %r16, 808(%r8)
	ld %r20, 936(%r8)
	ld %r17, 824(%r8)
	ld %r21, 952(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 776(%r8)
	std %r18, 904(%r8)
	std %r15, 792(%r8)
	std %r19, 920(%r8)
	std %r16, 808(%r8)
	std %r20, 936(%r8)
	std %r17, 824(%r8)
	std %r21, 952(%r8)
	ld %r14, 840(%r8)
	ld %r18, 968(%r8)
	ld %r15, 856(%r8)
	ld %r19, 984(%r8)
	ld %r16, 872(%r8)
	ld %r20, 1000(%r8)
	ld %r17, 888(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 840(%r8)
	std %r18, 968(%r8)
	std %r15, 856(%r8)
	std %r19, 984(%r8)
	std %r16, 872(%r8)
	std %r20, 1000(%r8)
	std %r17, 888(%r8)
	std %r21, 1016(%r8)
	ld %r22, 776(%r8)
	li %r12, 0
	stdbrx %r22, %r4, %r12
	ld %r22, 768(%r8)
	li %r12, 8
	stdbrx %r22, %r4, %r12
	addi %r4, %r4, 16
	subf %r22, %r11, %r10
	cmpldi %cr0, %r22, 0
	bne %cr0, 20b
	ld %r14, 3072(%r8)
	ld %r15, 3080(%r8)
	ld %r16, 3088(%r8)
	ld %r17, 3096(%r8)
	ld %r18, 3104(%r8)
	ld %r19, 3112(%r8)
	ld %r20, 3120(%r8)
	ld %r21, 3128(%r8)
	ld %r22, 3136(%r8)
	ld %r23, 3144(%r8)
	ld %r24, 3152(%r8)
	ld %r25, 3160(%r8)
	ld %r26, 3168(%r8)
	ld %r27, 3176(%r8)
	ld %r28, 3184(%r8)
	ld %r29, 3192(%r8)
	ld %r30, 3200(%r8)
	ld %r31, 3208(%r8)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	addi %r1, %r1, 3248
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_sm4_ecb_encrypt:
	stdu %r1, -3280(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 3232(%r6)
	std %r30, 3216(%r6)
	std %r31, 3224(%r6)
	or %r7, %r6, %r6
	or %r31, %r4, %r4
	or %r30, %r5, %r5
	li %r4, 0
	or %r5, %r7, %r7
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r5, %r30, %r30
	or %r8, %r7, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 23f
	or %r12, %r5, %r5
	b 24f
23:
	li %r12, 16
24:
	or %r6, %r31, %r31
	addi %r10, %r8, 768
	or %r3, %r12, %r12
25:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 25b
	or %r3, %r7, %r7
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r8, %r7, %r7
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 26f
	or %r12, %r5, %r5
	b 27f
26:
	li %r12, 16
27:
	addi %r6, %r8, 768
	or %r10, %r31, %r31
	or %r3, %r12, %r12
28:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 28b
	subf %r5, %r12, %r5
	addi %r31, %r31, 256
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r30, 3216(%r7)
	ld %r0, 3232(%r7)
	mtlr %r0
	ld %r31, 3224(%r7)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	addi %r1, %r1, 3280
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_sm4_ecb_decrypt:
	stdu %r1, -3280(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 3232(%r6)
	std %r30, 3216(%r6)
	std %r31, 3224(%r6)
	or %r7, %r6, %r6
	or %r31, %r4, %r4
	or %r30, %r5, %r5
	li %r4, 1
	or %r5, %r7, %r7
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r5, %r30, %r30
	or %r8, %r7, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 23f
	or %r12, %r5, %r5
	b 24f
23:
	li %r12, 16
24:
	or %r6, %r31, %r31
	addi %r10, %r8, 768
	or %r3, %r12, %r12
25:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 25b
	or %r3, %r7, %r7
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r8, %r7, %r7
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 26f
	or %r12, %r5, %r5
	b 27f
26:
	li %r12, 16
27:
	addi %r6, %r8, 768
	or %r10, %r31, %r31
	or %r3, %r12, %r12
28:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 28b
	subf %r5, %r12, %r5
	addi %r31, %r31, 256
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r30, 3216(%r7)
	ld %r0, 3232(%r7)
	mtlr %r0
	ld %r31, 3224(%r7)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	addi %r1, %r1, 3280
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr
