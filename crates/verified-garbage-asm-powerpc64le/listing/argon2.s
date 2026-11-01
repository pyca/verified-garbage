// The functions of `src/argon2.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress:
	std %r14, 2048(%r6)
	std %r15, 2056(%r6)
	std %r16, 2064(%r6)
	std %r17, 2072(%r6)
	std %r18, 2080(%r6)
	std %r19, 2088(%r6)
	std %r20, 2096(%r6)
	std %r21, 2104(%r6)
	std %r22, 2112(%r6)
	ld %r0, 0(%r3)
	ld %r22, 0(%r4)
	xor %r0, %r0, %r22
	std %r0, 0(%r6)
	std %r0, 1024(%r6)
	ld %r0, 8(%r3)
	ld %r22, 8(%r4)
	xor %r0, %r0, %r22
	std %r0, 8(%r6)
	std %r0, 1032(%r6)
	ld %r0, 16(%r3)
	ld %r22, 16(%r4)
	xor %r0, %r0, %r22
	std %r0, 16(%r6)
	std %r0, 1040(%r6)
	ld %r0, 24(%r3)
	ld %r22, 24(%r4)
	xor %r0, %r0, %r22
	std %r0, 24(%r6)
	std %r0, 1048(%r6)
	ld %r0, 32(%r3)
	ld %r22, 32(%r4)
	xor %r0, %r0, %r22
	std %r0, 32(%r6)
	std %r0, 1056(%r6)
	ld %r0, 40(%r3)
	ld %r22, 40(%r4)
	xor %r0, %r0, %r22
	std %r0, 40(%r6)
	std %r0, 1064(%r6)
	ld %r0, 48(%r3)
	ld %r22, 48(%r4)
	xor %r0, %r0, %r22
	std %r0, 48(%r6)
	std %r0, 1072(%r6)
	ld %r0, 56(%r3)
	ld %r22, 56(%r4)
	xor %r0, %r0, %r22
	std %r0, 56(%r6)
	std %r0, 1080(%r6)
	ld %r0, 64(%r3)
	ld %r22, 64(%r4)
	xor %r0, %r0, %r22
	std %r0, 64(%r6)
	std %r0, 1088(%r6)
	ld %r0, 72(%r3)
	ld %r22, 72(%r4)
	xor %r0, %r0, %r22
	std %r0, 72(%r6)
	std %r0, 1096(%r6)
	ld %r0, 80(%r3)
	ld %r22, 80(%r4)
	xor %r0, %r0, %r22
	std %r0, 80(%r6)
	std %r0, 1104(%r6)
	ld %r0, 88(%r3)
	ld %r22, 88(%r4)
	xor %r0, %r0, %r22
	std %r0, 88(%r6)
	std %r0, 1112(%r6)
	ld %r0, 96(%r3)
	ld %r22, 96(%r4)
	xor %r0, %r0, %r22
	std %r0, 96(%r6)
	std %r0, 1120(%r6)
	ld %r0, 104(%r3)
	ld %r22, 104(%r4)
	xor %r0, %r0, %r22
	std %r0, 104(%r6)
	std %r0, 1128(%r6)
	ld %r0, 112(%r3)
	ld %r22, 112(%r4)
	xor %r0, %r0, %r22
	std %r0, 112(%r6)
	std %r0, 1136(%r6)
	ld %r0, 120(%r3)
	ld %r22, 120(%r4)
	xor %r0, %r0, %r22
	std %r0, 120(%r6)
	std %r0, 1144(%r6)
	ld %r0, 128(%r3)
	ld %r22, 128(%r4)
	xor %r0, %r0, %r22
	std %r0, 128(%r6)
	std %r0, 1152(%r6)
	ld %r0, 136(%r3)
	ld %r22, 136(%r4)
	xor %r0, %r0, %r22
	std %r0, 136(%r6)
	std %r0, 1160(%r6)
	ld %r0, 144(%r3)
	ld %r22, 144(%r4)
	xor %r0, %r0, %r22
	std %r0, 144(%r6)
	std %r0, 1168(%r6)
	ld %r0, 152(%r3)
	ld %r22, 152(%r4)
	xor %r0, %r0, %r22
	std %r0, 152(%r6)
	std %r0, 1176(%r6)
	ld %r0, 160(%r3)
	ld %r22, 160(%r4)
	xor %r0, %r0, %r22
	std %r0, 160(%r6)
	std %r0, 1184(%r6)
	ld %r0, 168(%r3)
	ld %r22, 168(%r4)
	xor %r0, %r0, %r22
	std %r0, 168(%r6)
	std %r0, 1192(%r6)
	ld %r0, 176(%r3)
	ld %r22, 176(%r4)
	xor %r0, %r0, %r22
	std %r0, 176(%r6)
	std %r0, 1200(%r6)
	ld %r0, 184(%r3)
	ld %r22, 184(%r4)
	xor %r0, %r0, %r22
	std %r0, 184(%r6)
	std %r0, 1208(%r6)
	ld %r0, 192(%r3)
	ld %r22, 192(%r4)
	xor %r0, %r0, %r22
	std %r0, 192(%r6)
	std %r0, 1216(%r6)
	ld %r0, 200(%r3)
	ld %r22, 200(%r4)
	xor %r0, %r0, %r22
	std %r0, 200(%r6)
	std %r0, 1224(%r6)
	ld %r0, 208(%r3)
	ld %r22, 208(%r4)
	xor %r0, %r0, %r22
	std %r0, 208(%r6)
	std %r0, 1232(%r6)
	ld %r0, 216(%r3)
	ld %r22, 216(%r4)
	xor %r0, %r0, %r22
	std %r0, 216(%r6)
	std %r0, 1240(%r6)
	ld %r0, 224(%r3)
	ld %r22, 224(%r4)
	xor %r0, %r0, %r22
	std %r0, 224(%r6)
	std %r0, 1248(%r6)
	ld %r0, 232(%r3)
	ld %r22, 232(%r4)
	xor %r0, %r0, %r22
	std %r0, 232(%r6)
	std %r0, 1256(%r6)
	ld %r0, 240(%r3)
	ld %r22, 240(%r4)
	xor %r0, %r0, %r22
	std %r0, 240(%r6)
	std %r0, 1264(%r6)
	ld %r0, 248(%r3)
	ld %r22, 248(%r4)
	xor %r0, %r0, %r22
	std %r0, 248(%r6)
	std %r0, 1272(%r6)
	ld %r0, 256(%r3)
	ld %r22, 256(%r4)
	xor %r0, %r0, %r22
	std %r0, 256(%r6)
	std %r0, 1280(%r6)
	ld %r0, 264(%r3)
	ld %r22, 264(%r4)
	xor %r0, %r0, %r22
	std %r0, 264(%r6)
	std %r0, 1288(%r6)
	ld %r0, 272(%r3)
	ld %r22, 272(%r4)
	xor %r0, %r0, %r22
	std %r0, 272(%r6)
	std %r0, 1296(%r6)
	ld %r0, 280(%r3)
	ld %r22, 280(%r4)
	xor %r0, %r0, %r22
	std %r0, 280(%r6)
	std %r0, 1304(%r6)
	ld %r0, 288(%r3)
	ld %r22, 288(%r4)
	xor %r0, %r0, %r22
	std %r0, 288(%r6)
	std %r0, 1312(%r6)
	ld %r0, 296(%r3)
	ld %r22, 296(%r4)
	xor %r0, %r0, %r22
	std %r0, 296(%r6)
	std %r0, 1320(%r6)
	ld %r0, 304(%r3)
	ld %r22, 304(%r4)
	xor %r0, %r0, %r22
	std %r0, 304(%r6)
	std %r0, 1328(%r6)
	ld %r0, 312(%r3)
	ld %r22, 312(%r4)
	xor %r0, %r0, %r22
	std %r0, 312(%r6)
	std %r0, 1336(%r6)
	ld %r0, 320(%r3)
	ld %r22, 320(%r4)
	xor %r0, %r0, %r22
	std %r0, 320(%r6)
	std %r0, 1344(%r6)
	ld %r0, 328(%r3)
	ld %r22, 328(%r4)
	xor %r0, %r0, %r22
	std %r0, 328(%r6)
	std %r0, 1352(%r6)
	ld %r0, 336(%r3)
	ld %r22, 336(%r4)
	xor %r0, %r0, %r22
	std %r0, 336(%r6)
	std %r0, 1360(%r6)
	ld %r0, 344(%r3)
	ld %r22, 344(%r4)
	xor %r0, %r0, %r22
	std %r0, 344(%r6)
	std %r0, 1368(%r6)
	ld %r0, 352(%r3)
	ld %r22, 352(%r4)
	xor %r0, %r0, %r22
	std %r0, 352(%r6)
	std %r0, 1376(%r6)
	ld %r0, 360(%r3)
	ld %r22, 360(%r4)
	xor %r0, %r0, %r22
	std %r0, 360(%r6)
	std %r0, 1384(%r6)
	ld %r0, 368(%r3)
	ld %r22, 368(%r4)
	xor %r0, %r0, %r22
	std %r0, 368(%r6)
	std %r0, 1392(%r6)
	ld %r0, 376(%r3)
	ld %r22, 376(%r4)
	xor %r0, %r0, %r22
	std %r0, 376(%r6)
	std %r0, 1400(%r6)
	ld %r0, 384(%r3)
	ld %r22, 384(%r4)
	xor %r0, %r0, %r22
	std %r0, 384(%r6)
	std %r0, 1408(%r6)
	ld %r0, 392(%r3)
	ld %r22, 392(%r4)
	xor %r0, %r0, %r22
	std %r0, 392(%r6)
	std %r0, 1416(%r6)
	ld %r0, 400(%r3)
	ld %r22, 400(%r4)
	xor %r0, %r0, %r22
	std %r0, 400(%r6)
	std %r0, 1424(%r6)
	ld %r0, 408(%r3)
	ld %r22, 408(%r4)
	xor %r0, %r0, %r22
	std %r0, 408(%r6)
	std %r0, 1432(%r6)
	ld %r0, 416(%r3)
	ld %r22, 416(%r4)
	xor %r0, %r0, %r22
	std %r0, 416(%r6)
	std %r0, 1440(%r6)
	ld %r0, 424(%r3)
	ld %r22, 424(%r4)
	xor %r0, %r0, %r22
	std %r0, 424(%r6)
	std %r0, 1448(%r6)
	ld %r0, 432(%r3)
	ld %r22, 432(%r4)
	xor %r0, %r0, %r22
	std %r0, 432(%r6)
	std %r0, 1456(%r6)
	ld %r0, 440(%r3)
	ld %r22, 440(%r4)
	xor %r0, %r0, %r22
	std %r0, 440(%r6)
	std %r0, 1464(%r6)
	ld %r0, 448(%r3)
	ld %r22, 448(%r4)
	xor %r0, %r0, %r22
	std %r0, 448(%r6)
	std %r0, 1472(%r6)
	ld %r0, 456(%r3)
	ld %r22, 456(%r4)
	xor %r0, %r0, %r22
	std %r0, 456(%r6)
	std %r0, 1480(%r6)
	ld %r0, 464(%r3)
	ld %r22, 464(%r4)
	xor %r0, %r0, %r22
	std %r0, 464(%r6)
	std %r0, 1488(%r6)
	ld %r0, 472(%r3)
	ld %r22, 472(%r4)
	xor %r0, %r0, %r22
	std %r0, 472(%r6)
	std %r0, 1496(%r6)
	ld %r0, 480(%r3)
	ld %r22, 480(%r4)
	xor %r0, %r0, %r22
	std %r0, 480(%r6)
	std %r0, 1504(%r6)
	ld %r0, 488(%r3)
	ld %r22, 488(%r4)
	xor %r0, %r0, %r22
	std %r0, 488(%r6)
	std %r0, 1512(%r6)
	ld %r0, 496(%r3)
	ld %r22, 496(%r4)
	xor %r0, %r0, %r22
	std %r0, 496(%r6)
	std %r0, 1520(%r6)
	ld %r0, 504(%r3)
	ld %r22, 504(%r4)
	xor %r0, %r0, %r22
	std %r0, 504(%r6)
	std %r0, 1528(%r6)
	ld %r0, 512(%r3)
	ld %r22, 512(%r4)
	xor %r0, %r0, %r22
	std %r0, 512(%r6)
	std %r0, 1536(%r6)
	ld %r0, 520(%r3)
	ld %r22, 520(%r4)
	xor %r0, %r0, %r22
	std %r0, 520(%r6)
	std %r0, 1544(%r6)
	ld %r0, 528(%r3)
	ld %r22, 528(%r4)
	xor %r0, %r0, %r22
	std %r0, 528(%r6)
	std %r0, 1552(%r6)
	ld %r0, 536(%r3)
	ld %r22, 536(%r4)
	xor %r0, %r0, %r22
	std %r0, 536(%r6)
	std %r0, 1560(%r6)
	ld %r0, 544(%r3)
	ld %r22, 544(%r4)
	xor %r0, %r0, %r22
	std %r0, 544(%r6)
	std %r0, 1568(%r6)
	ld %r0, 552(%r3)
	ld %r22, 552(%r4)
	xor %r0, %r0, %r22
	std %r0, 552(%r6)
	std %r0, 1576(%r6)
	ld %r0, 560(%r3)
	ld %r22, 560(%r4)
	xor %r0, %r0, %r22
	std %r0, 560(%r6)
	std %r0, 1584(%r6)
	ld %r0, 568(%r3)
	ld %r22, 568(%r4)
	xor %r0, %r0, %r22
	std %r0, 568(%r6)
	std %r0, 1592(%r6)
	ld %r0, 576(%r3)
	ld %r22, 576(%r4)
	xor %r0, %r0, %r22
	std %r0, 576(%r6)
	std %r0, 1600(%r6)
	ld %r0, 584(%r3)
	ld %r22, 584(%r4)
	xor %r0, %r0, %r22
	std %r0, 584(%r6)
	std %r0, 1608(%r6)
	ld %r0, 592(%r3)
	ld %r22, 592(%r4)
	xor %r0, %r0, %r22
	std %r0, 592(%r6)
	std %r0, 1616(%r6)
	ld %r0, 600(%r3)
	ld %r22, 600(%r4)
	xor %r0, %r0, %r22
	std %r0, 600(%r6)
	std %r0, 1624(%r6)
	ld %r0, 608(%r3)
	ld %r22, 608(%r4)
	xor %r0, %r0, %r22
	std %r0, 608(%r6)
	std %r0, 1632(%r6)
	ld %r0, 616(%r3)
	ld %r22, 616(%r4)
	xor %r0, %r0, %r22
	std %r0, 616(%r6)
	std %r0, 1640(%r6)
	ld %r0, 624(%r3)
	ld %r22, 624(%r4)
	xor %r0, %r0, %r22
	std %r0, 624(%r6)
	std %r0, 1648(%r6)
	ld %r0, 632(%r3)
	ld %r22, 632(%r4)
	xor %r0, %r0, %r22
	std %r0, 632(%r6)
	std %r0, 1656(%r6)
	ld %r0, 640(%r3)
	ld %r22, 640(%r4)
	xor %r0, %r0, %r22
	std %r0, 640(%r6)
	std %r0, 1664(%r6)
	ld %r0, 648(%r3)
	ld %r22, 648(%r4)
	xor %r0, %r0, %r22
	std %r0, 648(%r6)
	std %r0, 1672(%r6)
	ld %r0, 656(%r3)
	ld %r22, 656(%r4)
	xor %r0, %r0, %r22
	std %r0, 656(%r6)
	std %r0, 1680(%r6)
	ld %r0, 664(%r3)
	ld %r22, 664(%r4)
	xor %r0, %r0, %r22
	std %r0, 664(%r6)
	std %r0, 1688(%r6)
	ld %r0, 672(%r3)
	ld %r22, 672(%r4)
	xor %r0, %r0, %r22
	std %r0, 672(%r6)
	std %r0, 1696(%r6)
	ld %r0, 680(%r3)
	ld %r22, 680(%r4)
	xor %r0, %r0, %r22
	std %r0, 680(%r6)
	std %r0, 1704(%r6)
	ld %r0, 688(%r3)
	ld %r22, 688(%r4)
	xor %r0, %r0, %r22
	std %r0, 688(%r6)
	std %r0, 1712(%r6)
	ld %r0, 696(%r3)
	ld %r22, 696(%r4)
	xor %r0, %r0, %r22
	std %r0, 696(%r6)
	std %r0, 1720(%r6)
	ld %r0, 704(%r3)
	ld %r22, 704(%r4)
	xor %r0, %r0, %r22
	std %r0, 704(%r6)
	std %r0, 1728(%r6)
	ld %r0, 712(%r3)
	ld %r22, 712(%r4)
	xor %r0, %r0, %r22
	std %r0, 712(%r6)
	std %r0, 1736(%r6)
	ld %r0, 720(%r3)
	ld %r22, 720(%r4)
	xor %r0, %r0, %r22
	std %r0, 720(%r6)
	std %r0, 1744(%r6)
	ld %r0, 728(%r3)
	ld %r22, 728(%r4)
	xor %r0, %r0, %r22
	std %r0, 728(%r6)
	std %r0, 1752(%r6)
	ld %r0, 736(%r3)
	ld %r22, 736(%r4)
	xor %r0, %r0, %r22
	std %r0, 736(%r6)
	std %r0, 1760(%r6)
	ld %r0, 744(%r3)
	ld %r22, 744(%r4)
	xor %r0, %r0, %r22
	std %r0, 744(%r6)
	std %r0, 1768(%r6)
	ld %r0, 752(%r3)
	ld %r22, 752(%r4)
	xor %r0, %r0, %r22
	std %r0, 752(%r6)
	std %r0, 1776(%r6)
	ld %r0, 760(%r3)
	ld %r22, 760(%r4)
	xor %r0, %r0, %r22
	std %r0, 760(%r6)
	std %r0, 1784(%r6)
	ld %r0, 768(%r3)
	ld %r22, 768(%r4)
	xor %r0, %r0, %r22
	std %r0, 768(%r6)
	std %r0, 1792(%r6)
	ld %r0, 776(%r3)
	ld %r22, 776(%r4)
	xor %r0, %r0, %r22
	std %r0, 776(%r6)
	std %r0, 1800(%r6)
	ld %r0, 784(%r3)
	ld %r22, 784(%r4)
	xor %r0, %r0, %r22
	std %r0, 784(%r6)
	std %r0, 1808(%r6)
	ld %r0, 792(%r3)
	ld %r22, 792(%r4)
	xor %r0, %r0, %r22
	std %r0, 792(%r6)
	std %r0, 1816(%r6)
	ld %r0, 800(%r3)
	ld %r22, 800(%r4)
	xor %r0, %r0, %r22
	std %r0, 800(%r6)
	std %r0, 1824(%r6)
	ld %r0, 808(%r3)
	ld %r22, 808(%r4)
	xor %r0, %r0, %r22
	std %r0, 808(%r6)
	std %r0, 1832(%r6)
	ld %r0, 816(%r3)
	ld %r22, 816(%r4)
	xor %r0, %r0, %r22
	std %r0, 816(%r6)
	std %r0, 1840(%r6)
	ld %r0, 824(%r3)
	ld %r22, 824(%r4)
	xor %r0, %r0, %r22
	std %r0, 824(%r6)
	std %r0, 1848(%r6)
	ld %r0, 832(%r3)
	ld %r22, 832(%r4)
	xor %r0, %r0, %r22
	std %r0, 832(%r6)
	std %r0, 1856(%r6)
	ld %r0, 840(%r3)
	ld %r22, 840(%r4)
	xor %r0, %r0, %r22
	std %r0, 840(%r6)
	std %r0, 1864(%r6)
	ld %r0, 848(%r3)
	ld %r22, 848(%r4)
	xor %r0, %r0, %r22
	std %r0, 848(%r6)
	std %r0, 1872(%r6)
	ld %r0, 856(%r3)
	ld %r22, 856(%r4)
	xor %r0, %r0, %r22
	std %r0, 856(%r6)
	std %r0, 1880(%r6)
	ld %r0, 864(%r3)
	ld %r22, 864(%r4)
	xor %r0, %r0, %r22
	std %r0, 864(%r6)
	std %r0, 1888(%r6)
	ld %r0, 872(%r3)
	ld %r22, 872(%r4)
	xor %r0, %r0, %r22
	std %r0, 872(%r6)
	std %r0, 1896(%r6)
	ld %r0, 880(%r3)
	ld %r22, 880(%r4)
	xor %r0, %r0, %r22
	std %r0, 880(%r6)
	std %r0, 1904(%r6)
	ld %r0, 888(%r3)
	ld %r22, 888(%r4)
	xor %r0, %r0, %r22
	std %r0, 888(%r6)
	std %r0, 1912(%r6)
	ld %r0, 896(%r3)
	ld %r22, 896(%r4)
	xor %r0, %r0, %r22
	std %r0, 896(%r6)
	std %r0, 1920(%r6)
	ld %r0, 904(%r3)
	ld %r22, 904(%r4)
	xor %r0, %r0, %r22
	std %r0, 904(%r6)
	std %r0, 1928(%r6)
	ld %r0, 912(%r3)
	ld %r22, 912(%r4)
	xor %r0, %r0, %r22
	std %r0, 912(%r6)
	std %r0, 1936(%r6)
	ld %r0, 920(%r3)
	ld %r22, 920(%r4)
	xor %r0, %r0, %r22
	std %r0, 920(%r6)
	std %r0, 1944(%r6)
	ld %r0, 928(%r3)
	ld %r22, 928(%r4)
	xor %r0, %r0, %r22
	std %r0, 928(%r6)
	std %r0, 1952(%r6)
	ld %r0, 936(%r3)
	ld %r22, 936(%r4)
	xor %r0, %r0, %r22
	std %r0, 936(%r6)
	std %r0, 1960(%r6)
	ld %r0, 944(%r3)
	ld %r22, 944(%r4)
	xor %r0, %r0, %r22
	std %r0, 944(%r6)
	std %r0, 1968(%r6)
	ld %r0, 952(%r3)
	ld %r22, 952(%r4)
	xor %r0, %r0, %r22
	std %r0, 952(%r6)
	std %r0, 1976(%r6)
	ld %r0, 960(%r3)
	ld %r22, 960(%r4)
	xor %r0, %r0, %r22
	std %r0, 960(%r6)
	std %r0, 1984(%r6)
	ld %r0, 968(%r3)
	ld %r22, 968(%r4)
	xor %r0, %r0, %r22
	std %r0, 968(%r6)
	std %r0, 1992(%r6)
	ld %r0, 976(%r3)
	ld %r22, 976(%r4)
	xor %r0, %r0, %r22
	std %r0, 976(%r6)
	std %r0, 2000(%r6)
	ld %r0, 984(%r3)
	ld %r22, 984(%r4)
	xor %r0, %r0, %r22
	std %r0, 984(%r6)
	std %r0, 2008(%r6)
	ld %r0, 992(%r3)
	ld %r22, 992(%r4)
	xor %r0, %r0, %r22
	std %r0, 992(%r6)
	std %r0, 2016(%r6)
	ld %r0, 1000(%r3)
	ld %r22, 1000(%r4)
	xor %r0, %r0, %r22
	std %r0, 1000(%r6)
	std %r0, 2024(%r6)
	ld %r0, 1008(%r3)
	ld %r22, 1008(%r4)
	xor %r0, %r0, %r22
	std %r0, 1008(%r6)
	std %r0, 2032(%r6)
	ld %r0, 1016(%r3)
	ld %r22, 1016(%r4)
	xor %r0, %r0, %r22
	std %r0, 1016(%r6)
	std %r0, 2040(%r6)
	ld %r3, 1024(%r6)
	ld %r4, 1032(%r6)
	ld %r7, 1040(%r6)
	ld %r8, 1048(%r6)
	ld %r9, 1056(%r6)
	ld %r10, 1064(%r6)
	ld %r11, 1072(%r6)
	ld %r12, 1080(%r6)
	ld %r14, 1088(%r6)
	ld %r15, 1096(%r6)
	ld %r16, 1104(%r6)
	ld %r17, 1112(%r6)
	ld %r18, 1120(%r6)
	ld %r19, 1128(%r6)
	ld %r20, 1136(%r6)
	ld %r21, 1144(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1024(%r6)
	std %r4, 1032(%r6)
	std %r7, 1040(%r6)
	std %r8, 1048(%r6)
	std %r9, 1056(%r6)
	std %r10, 1064(%r6)
	std %r11, 1072(%r6)
	std %r12, 1080(%r6)
	std %r14, 1088(%r6)
	std %r15, 1096(%r6)
	std %r16, 1104(%r6)
	std %r17, 1112(%r6)
	std %r18, 1120(%r6)
	std %r19, 1128(%r6)
	std %r20, 1136(%r6)
	std %r21, 1144(%r6)
	ld %r3, 1152(%r6)
	ld %r4, 1160(%r6)
	ld %r7, 1168(%r6)
	ld %r8, 1176(%r6)
	ld %r9, 1184(%r6)
	ld %r10, 1192(%r6)
	ld %r11, 1200(%r6)
	ld %r12, 1208(%r6)
	ld %r14, 1216(%r6)
	ld %r15, 1224(%r6)
	ld %r16, 1232(%r6)
	ld %r17, 1240(%r6)
	ld %r18, 1248(%r6)
	ld %r19, 1256(%r6)
	ld %r20, 1264(%r6)
	ld %r21, 1272(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1152(%r6)
	std %r4, 1160(%r6)
	std %r7, 1168(%r6)
	std %r8, 1176(%r6)
	std %r9, 1184(%r6)
	std %r10, 1192(%r6)
	std %r11, 1200(%r6)
	std %r12, 1208(%r6)
	std %r14, 1216(%r6)
	std %r15, 1224(%r6)
	std %r16, 1232(%r6)
	std %r17, 1240(%r6)
	std %r18, 1248(%r6)
	std %r19, 1256(%r6)
	std %r20, 1264(%r6)
	std %r21, 1272(%r6)
	ld %r3, 1280(%r6)
	ld %r4, 1288(%r6)
	ld %r7, 1296(%r6)
	ld %r8, 1304(%r6)
	ld %r9, 1312(%r6)
	ld %r10, 1320(%r6)
	ld %r11, 1328(%r6)
	ld %r12, 1336(%r6)
	ld %r14, 1344(%r6)
	ld %r15, 1352(%r6)
	ld %r16, 1360(%r6)
	ld %r17, 1368(%r6)
	ld %r18, 1376(%r6)
	ld %r19, 1384(%r6)
	ld %r20, 1392(%r6)
	ld %r21, 1400(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1280(%r6)
	std %r4, 1288(%r6)
	std %r7, 1296(%r6)
	std %r8, 1304(%r6)
	std %r9, 1312(%r6)
	std %r10, 1320(%r6)
	std %r11, 1328(%r6)
	std %r12, 1336(%r6)
	std %r14, 1344(%r6)
	std %r15, 1352(%r6)
	std %r16, 1360(%r6)
	std %r17, 1368(%r6)
	std %r18, 1376(%r6)
	std %r19, 1384(%r6)
	std %r20, 1392(%r6)
	std %r21, 1400(%r6)
	ld %r3, 1408(%r6)
	ld %r4, 1416(%r6)
	ld %r7, 1424(%r6)
	ld %r8, 1432(%r6)
	ld %r9, 1440(%r6)
	ld %r10, 1448(%r6)
	ld %r11, 1456(%r6)
	ld %r12, 1464(%r6)
	ld %r14, 1472(%r6)
	ld %r15, 1480(%r6)
	ld %r16, 1488(%r6)
	ld %r17, 1496(%r6)
	ld %r18, 1504(%r6)
	ld %r19, 1512(%r6)
	ld %r20, 1520(%r6)
	ld %r21, 1528(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1408(%r6)
	std %r4, 1416(%r6)
	std %r7, 1424(%r6)
	std %r8, 1432(%r6)
	std %r9, 1440(%r6)
	std %r10, 1448(%r6)
	std %r11, 1456(%r6)
	std %r12, 1464(%r6)
	std %r14, 1472(%r6)
	std %r15, 1480(%r6)
	std %r16, 1488(%r6)
	std %r17, 1496(%r6)
	std %r18, 1504(%r6)
	std %r19, 1512(%r6)
	std %r20, 1520(%r6)
	std %r21, 1528(%r6)
	ld %r3, 1536(%r6)
	ld %r4, 1544(%r6)
	ld %r7, 1552(%r6)
	ld %r8, 1560(%r6)
	ld %r9, 1568(%r6)
	ld %r10, 1576(%r6)
	ld %r11, 1584(%r6)
	ld %r12, 1592(%r6)
	ld %r14, 1600(%r6)
	ld %r15, 1608(%r6)
	ld %r16, 1616(%r6)
	ld %r17, 1624(%r6)
	ld %r18, 1632(%r6)
	ld %r19, 1640(%r6)
	ld %r20, 1648(%r6)
	ld %r21, 1656(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1536(%r6)
	std %r4, 1544(%r6)
	std %r7, 1552(%r6)
	std %r8, 1560(%r6)
	std %r9, 1568(%r6)
	std %r10, 1576(%r6)
	std %r11, 1584(%r6)
	std %r12, 1592(%r6)
	std %r14, 1600(%r6)
	std %r15, 1608(%r6)
	std %r16, 1616(%r6)
	std %r17, 1624(%r6)
	std %r18, 1632(%r6)
	std %r19, 1640(%r6)
	std %r20, 1648(%r6)
	std %r21, 1656(%r6)
	ld %r3, 1664(%r6)
	ld %r4, 1672(%r6)
	ld %r7, 1680(%r6)
	ld %r8, 1688(%r6)
	ld %r9, 1696(%r6)
	ld %r10, 1704(%r6)
	ld %r11, 1712(%r6)
	ld %r12, 1720(%r6)
	ld %r14, 1728(%r6)
	ld %r15, 1736(%r6)
	ld %r16, 1744(%r6)
	ld %r17, 1752(%r6)
	ld %r18, 1760(%r6)
	ld %r19, 1768(%r6)
	ld %r20, 1776(%r6)
	ld %r21, 1784(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1664(%r6)
	std %r4, 1672(%r6)
	std %r7, 1680(%r6)
	std %r8, 1688(%r6)
	std %r9, 1696(%r6)
	std %r10, 1704(%r6)
	std %r11, 1712(%r6)
	std %r12, 1720(%r6)
	std %r14, 1728(%r6)
	std %r15, 1736(%r6)
	std %r16, 1744(%r6)
	std %r17, 1752(%r6)
	std %r18, 1760(%r6)
	std %r19, 1768(%r6)
	std %r20, 1776(%r6)
	std %r21, 1784(%r6)
	ld %r3, 1792(%r6)
	ld %r4, 1800(%r6)
	ld %r7, 1808(%r6)
	ld %r8, 1816(%r6)
	ld %r9, 1824(%r6)
	ld %r10, 1832(%r6)
	ld %r11, 1840(%r6)
	ld %r12, 1848(%r6)
	ld %r14, 1856(%r6)
	ld %r15, 1864(%r6)
	ld %r16, 1872(%r6)
	ld %r17, 1880(%r6)
	ld %r18, 1888(%r6)
	ld %r19, 1896(%r6)
	ld %r20, 1904(%r6)
	ld %r21, 1912(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1792(%r6)
	std %r4, 1800(%r6)
	std %r7, 1808(%r6)
	std %r8, 1816(%r6)
	std %r9, 1824(%r6)
	std %r10, 1832(%r6)
	std %r11, 1840(%r6)
	std %r12, 1848(%r6)
	std %r14, 1856(%r6)
	std %r15, 1864(%r6)
	std %r16, 1872(%r6)
	std %r17, 1880(%r6)
	std %r18, 1888(%r6)
	std %r19, 1896(%r6)
	std %r20, 1904(%r6)
	std %r21, 1912(%r6)
	ld %r3, 1920(%r6)
	ld %r4, 1928(%r6)
	ld %r7, 1936(%r6)
	ld %r8, 1944(%r6)
	ld %r9, 1952(%r6)
	ld %r10, 1960(%r6)
	ld %r11, 1968(%r6)
	ld %r12, 1976(%r6)
	ld %r14, 1984(%r6)
	ld %r15, 1992(%r6)
	ld %r16, 2000(%r6)
	ld %r17, 2008(%r6)
	ld %r18, 2016(%r6)
	ld %r19, 2024(%r6)
	ld %r20, 2032(%r6)
	ld %r21, 2040(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1920(%r6)
	std %r4, 1928(%r6)
	std %r7, 1936(%r6)
	std %r8, 1944(%r6)
	std %r9, 1952(%r6)
	std %r10, 1960(%r6)
	std %r11, 1968(%r6)
	std %r12, 1976(%r6)
	std %r14, 1984(%r6)
	std %r15, 1992(%r6)
	std %r16, 2000(%r6)
	std %r17, 2008(%r6)
	std %r18, 2016(%r6)
	std %r19, 2024(%r6)
	std %r20, 2032(%r6)
	std %r21, 2040(%r6)
	ld %r3, 1024(%r6)
	ld %r4, 1032(%r6)
	ld %r7, 1152(%r6)
	ld %r8, 1160(%r6)
	ld %r9, 1280(%r6)
	ld %r10, 1288(%r6)
	ld %r11, 1408(%r6)
	ld %r12, 1416(%r6)
	ld %r14, 1536(%r6)
	ld %r15, 1544(%r6)
	ld %r16, 1664(%r6)
	ld %r17, 1672(%r6)
	ld %r18, 1792(%r6)
	ld %r19, 1800(%r6)
	ld %r20, 1920(%r6)
	ld %r21, 1928(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1024(%r6)
	std %r4, 1032(%r6)
	std %r7, 1152(%r6)
	std %r8, 1160(%r6)
	std %r9, 1280(%r6)
	std %r10, 1288(%r6)
	std %r11, 1408(%r6)
	std %r12, 1416(%r6)
	std %r14, 1536(%r6)
	std %r15, 1544(%r6)
	std %r16, 1664(%r6)
	std %r17, 1672(%r6)
	std %r18, 1792(%r6)
	std %r19, 1800(%r6)
	std %r20, 1920(%r6)
	std %r21, 1928(%r6)
	ld %r3, 1040(%r6)
	ld %r4, 1048(%r6)
	ld %r7, 1168(%r6)
	ld %r8, 1176(%r6)
	ld %r9, 1296(%r6)
	ld %r10, 1304(%r6)
	ld %r11, 1424(%r6)
	ld %r12, 1432(%r6)
	ld %r14, 1552(%r6)
	ld %r15, 1560(%r6)
	ld %r16, 1680(%r6)
	ld %r17, 1688(%r6)
	ld %r18, 1808(%r6)
	ld %r19, 1816(%r6)
	ld %r20, 1936(%r6)
	ld %r21, 1944(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1040(%r6)
	std %r4, 1048(%r6)
	std %r7, 1168(%r6)
	std %r8, 1176(%r6)
	std %r9, 1296(%r6)
	std %r10, 1304(%r6)
	std %r11, 1424(%r6)
	std %r12, 1432(%r6)
	std %r14, 1552(%r6)
	std %r15, 1560(%r6)
	std %r16, 1680(%r6)
	std %r17, 1688(%r6)
	std %r18, 1808(%r6)
	std %r19, 1816(%r6)
	std %r20, 1936(%r6)
	std %r21, 1944(%r6)
	ld %r3, 1056(%r6)
	ld %r4, 1064(%r6)
	ld %r7, 1184(%r6)
	ld %r8, 1192(%r6)
	ld %r9, 1312(%r6)
	ld %r10, 1320(%r6)
	ld %r11, 1440(%r6)
	ld %r12, 1448(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1696(%r6)
	ld %r17, 1704(%r6)
	ld %r18, 1824(%r6)
	ld %r19, 1832(%r6)
	ld %r20, 1952(%r6)
	ld %r21, 1960(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1056(%r6)
	std %r4, 1064(%r6)
	std %r7, 1184(%r6)
	std %r8, 1192(%r6)
	std %r9, 1312(%r6)
	std %r10, 1320(%r6)
	std %r11, 1440(%r6)
	std %r12, 1448(%r6)
	std %r14, 1568(%r6)
	std %r15, 1576(%r6)
	std %r16, 1696(%r6)
	std %r17, 1704(%r6)
	std %r18, 1824(%r6)
	std %r19, 1832(%r6)
	std %r20, 1952(%r6)
	std %r21, 1960(%r6)
	ld %r3, 1072(%r6)
	ld %r4, 1080(%r6)
	ld %r7, 1200(%r6)
	ld %r8, 1208(%r6)
	ld %r9, 1328(%r6)
	ld %r10, 1336(%r6)
	ld %r11, 1456(%r6)
	ld %r12, 1464(%r6)
	ld %r14, 1584(%r6)
	ld %r15, 1592(%r6)
	ld %r16, 1712(%r6)
	ld %r17, 1720(%r6)
	ld %r18, 1840(%r6)
	ld %r19, 1848(%r6)
	ld %r20, 1968(%r6)
	ld %r21, 1976(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1072(%r6)
	std %r4, 1080(%r6)
	std %r7, 1200(%r6)
	std %r8, 1208(%r6)
	std %r9, 1328(%r6)
	std %r10, 1336(%r6)
	std %r11, 1456(%r6)
	std %r12, 1464(%r6)
	std %r14, 1584(%r6)
	std %r15, 1592(%r6)
	std %r16, 1712(%r6)
	std %r17, 1720(%r6)
	std %r18, 1840(%r6)
	std %r19, 1848(%r6)
	std %r20, 1968(%r6)
	std %r21, 1976(%r6)
	ld %r3, 1088(%r6)
	ld %r4, 1096(%r6)
	ld %r7, 1216(%r6)
	ld %r8, 1224(%r6)
	ld %r9, 1344(%r6)
	ld %r10, 1352(%r6)
	ld %r11, 1472(%r6)
	ld %r12, 1480(%r6)
	ld %r14, 1600(%r6)
	ld %r15, 1608(%r6)
	ld %r16, 1728(%r6)
	ld %r17, 1736(%r6)
	ld %r18, 1856(%r6)
	ld %r19, 1864(%r6)
	ld %r20, 1984(%r6)
	ld %r21, 1992(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1088(%r6)
	std %r4, 1096(%r6)
	std %r7, 1216(%r6)
	std %r8, 1224(%r6)
	std %r9, 1344(%r6)
	std %r10, 1352(%r6)
	std %r11, 1472(%r6)
	std %r12, 1480(%r6)
	std %r14, 1600(%r6)
	std %r15, 1608(%r6)
	std %r16, 1728(%r6)
	std %r17, 1736(%r6)
	std %r18, 1856(%r6)
	std %r19, 1864(%r6)
	std %r20, 1984(%r6)
	std %r21, 1992(%r6)
	ld %r3, 1104(%r6)
	ld %r4, 1112(%r6)
	ld %r7, 1232(%r6)
	ld %r8, 1240(%r6)
	ld %r9, 1360(%r6)
	ld %r10, 1368(%r6)
	ld %r11, 1488(%r6)
	ld %r12, 1496(%r6)
	ld %r14, 1616(%r6)
	ld %r15, 1624(%r6)
	ld %r16, 1744(%r6)
	ld %r17, 1752(%r6)
	ld %r18, 1872(%r6)
	ld %r19, 1880(%r6)
	ld %r20, 2000(%r6)
	ld %r21, 2008(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1104(%r6)
	std %r4, 1112(%r6)
	std %r7, 1232(%r6)
	std %r8, 1240(%r6)
	std %r9, 1360(%r6)
	std %r10, 1368(%r6)
	std %r11, 1488(%r6)
	std %r12, 1496(%r6)
	std %r14, 1616(%r6)
	std %r15, 1624(%r6)
	std %r16, 1744(%r6)
	std %r17, 1752(%r6)
	std %r18, 1872(%r6)
	std %r19, 1880(%r6)
	std %r20, 2000(%r6)
	std %r21, 2008(%r6)
	ld %r3, 1120(%r6)
	ld %r4, 1128(%r6)
	ld %r7, 1248(%r6)
	ld %r8, 1256(%r6)
	ld %r9, 1376(%r6)
	ld %r10, 1384(%r6)
	ld %r11, 1504(%r6)
	ld %r12, 1512(%r6)
	ld %r14, 1632(%r6)
	ld %r15, 1640(%r6)
	ld %r16, 1760(%r6)
	ld %r17, 1768(%r6)
	ld %r18, 1888(%r6)
	ld %r19, 1896(%r6)
	ld %r20, 2016(%r6)
	ld %r21, 2024(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1120(%r6)
	std %r4, 1128(%r6)
	std %r7, 1248(%r6)
	std %r8, 1256(%r6)
	std %r9, 1376(%r6)
	std %r10, 1384(%r6)
	std %r11, 1504(%r6)
	std %r12, 1512(%r6)
	std %r14, 1632(%r6)
	std %r15, 1640(%r6)
	std %r16, 1760(%r6)
	std %r17, 1768(%r6)
	std %r18, 1888(%r6)
	std %r19, 1896(%r6)
	std %r20, 2016(%r6)
	std %r21, 2024(%r6)
	ld %r3, 1136(%r6)
	ld %r4, 1144(%r6)
	ld %r7, 1264(%r6)
	ld %r8, 1272(%r6)
	ld %r9, 1392(%r6)
	ld %r10, 1400(%r6)
	ld %r11, 1520(%r6)
	ld %r12, 1528(%r6)
	ld %r14, 1648(%r6)
	ld %r15, 1656(%r6)
	ld %r16, 1776(%r6)
	ld %r17, 1784(%r6)
	ld %r18, 1904(%r6)
	ld %r19, 1912(%r6)
	ld %r20, 2032(%r6)
	ld %r21, 2040(%r6)
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r9
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r18, %r18, %r3
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r18
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r9, %r9, %r14
	rldicl %r9, %r9, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r10
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r19, %r19, %r4
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r19
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r10, %r10, %r15
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r11
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r20
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r12
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r21, %r21, %r8
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r21
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 32, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 40, 0
	rlwinm %r0, %r3, 0, 0, 31
	rlwinm %r22, %r10, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r3, %r3, %r10
	add %r3, %r3, %r0
	add %r3, %r3, %r0
	xor %r21, %r21, %r3
	rldicl %r21, %r21, 48, 0
	rlwinm %r0, %r16, 0, 0, 31
	rlwinm %r22, %r21, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r16, %r16, %r21
	add %r16, %r16, %r0
	add %r16, %r16, %r0
	xor %r10, %r10, %r16
	rldicl %r10, %r10, 1, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 32, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	rlwinm %r0, %r4, 0, 0, 31
	rlwinm %r22, %r11, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r4, %r4, %r11
	add %r4, %r4, %r0
	add %r4, %r4, %r0
	xor %r18, %r18, %r4
	rldicl %r18, %r18, 48, 0
	rlwinm %r0, %r17, 0, 0, 31
	rlwinm %r22, %r18, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r17, %r17, %r18
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 32, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 40, 0
	rlwinm %r0, %r7, 0, 0, 31
	rlwinm %r22, %r12, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r0
	xor %r19, %r19, %r7
	rldicl %r19, %r19, 48, 0
	rlwinm %r0, %r14, 0, 0, 31
	rlwinm %r22, %r19, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r14, %r14, %r19
	add %r14, %r14, %r0
	add %r14, %r14, %r0
	xor %r12, %r12, %r14
	rldicl %r12, %r12, 1, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 32, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 40, 0
	rlwinm %r0, %r8, 0, 0, 31
	rlwinm %r22, %r9, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r8, %r8, %r9
	add %r8, %r8, %r0
	add %r8, %r8, %r0
	xor %r20, %r20, %r8
	rldicl %r20, %r20, 48, 0
	rlwinm %r0, %r15, 0, 0, 31
	rlwinm %r22, %r20, 0, 0, 31
	mulld %r0, %r0, %r22
	add %r15, %r15, %r20
	add %r15, %r15, %r0
	add %r15, %r15, %r0
	xor %r9, %r9, %r15
	rldicl %r9, %r9, 1, 0
	std %r3, 1136(%r6)
	std %r4, 1144(%r6)
	std %r7, 1264(%r6)
	std %r8, 1272(%r6)
	std %r9, 1392(%r6)
	std %r10, 1400(%r6)
	std %r11, 1520(%r6)
	std %r12, 1528(%r6)
	std %r14, 1648(%r6)
	std %r15, 1656(%r6)
	std %r16, 1776(%r6)
	std %r17, 1784(%r6)
	std %r18, 1904(%r6)
	std %r19, 1912(%r6)
	std %r20, 2032(%r6)
	std %r21, 2040(%r6)
	ld %r0, 1024(%r6)
	ld %r22, 0(%r6)
	xor %r0, %r0, %r22
	std %r0, 0(%r5)
	ld %r0, 1032(%r6)
	ld %r22, 8(%r6)
	xor %r0, %r0, %r22
	std %r0, 8(%r5)
	ld %r0, 1040(%r6)
	ld %r22, 16(%r6)
	xor %r0, %r0, %r22
	std %r0, 16(%r5)
	ld %r0, 1048(%r6)
	ld %r22, 24(%r6)
	xor %r0, %r0, %r22
	std %r0, 24(%r5)
	ld %r0, 1056(%r6)
	ld %r22, 32(%r6)
	xor %r0, %r0, %r22
	std %r0, 32(%r5)
	ld %r0, 1064(%r6)
	ld %r22, 40(%r6)
	xor %r0, %r0, %r22
	std %r0, 40(%r5)
	ld %r0, 1072(%r6)
	ld %r22, 48(%r6)
	xor %r0, %r0, %r22
	std %r0, 48(%r5)
	ld %r0, 1080(%r6)
	ld %r22, 56(%r6)
	xor %r0, %r0, %r22
	std %r0, 56(%r5)
	ld %r0, 1088(%r6)
	ld %r22, 64(%r6)
	xor %r0, %r0, %r22
	std %r0, 64(%r5)
	ld %r0, 1096(%r6)
	ld %r22, 72(%r6)
	xor %r0, %r0, %r22
	std %r0, 72(%r5)
	ld %r0, 1104(%r6)
	ld %r22, 80(%r6)
	xor %r0, %r0, %r22
	std %r0, 80(%r5)
	ld %r0, 1112(%r6)
	ld %r22, 88(%r6)
	xor %r0, %r0, %r22
	std %r0, 88(%r5)
	ld %r0, 1120(%r6)
	ld %r22, 96(%r6)
	xor %r0, %r0, %r22
	std %r0, 96(%r5)
	ld %r0, 1128(%r6)
	ld %r22, 104(%r6)
	xor %r0, %r0, %r22
	std %r0, 104(%r5)
	ld %r0, 1136(%r6)
	ld %r22, 112(%r6)
	xor %r0, %r0, %r22
	std %r0, 112(%r5)
	ld %r0, 1144(%r6)
	ld %r22, 120(%r6)
	xor %r0, %r0, %r22
	std %r0, 120(%r5)
	ld %r0, 1152(%r6)
	ld %r22, 128(%r6)
	xor %r0, %r0, %r22
	std %r0, 128(%r5)
	ld %r0, 1160(%r6)
	ld %r22, 136(%r6)
	xor %r0, %r0, %r22
	std %r0, 136(%r5)
	ld %r0, 1168(%r6)
	ld %r22, 144(%r6)
	xor %r0, %r0, %r22
	std %r0, 144(%r5)
	ld %r0, 1176(%r6)
	ld %r22, 152(%r6)
	xor %r0, %r0, %r22
	std %r0, 152(%r5)
	ld %r0, 1184(%r6)
	ld %r22, 160(%r6)
	xor %r0, %r0, %r22
	std %r0, 160(%r5)
	ld %r0, 1192(%r6)
	ld %r22, 168(%r6)
	xor %r0, %r0, %r22
	std %r0, 168(%r5)
	ld %r0, 1200(%r6)
	ld %r22, 176(%r6)
	xor %r0, %r0, %r22
	std %r0, 176(%r5)
	ld %r0, 1208(%r6)
	ld %r22, 184(%r6)
	xor %r0, %r0, %r22
	std %r0, 184(%r5)
	ld %r0, 1216(%r6)
	ld %r22, 192(%r6)
	xor %r0, %r0, %r22
	std %r0, 192(%r5)
	ld %r0, 1224(%r6)
	ld %r22, 200(%r6)
	xor %r0, %r0, %r22
	std %r0, 200(%r5)
	ld %r0, 1232(%r6)
	ld %r22, 208(%r6)
	xor %r0, %r0, %r22
	std %r0, 208(%r5)
	ld %r0, 1240(%r6)
	ld %r22, 216(%r6)
	xor %r0, %r0, %r22
	std %r0, 216(%r5)
	ld %r0, 1248(%r6)
	ld %r22, 224(%r6)
	xor %r0, %r0, %r22
	std %r0, 224(%r5)
	ld %r0, 1256(%r6)
	ld %r22, 232(%r6)
	xor %r0, %r0, %r22
	std %r0, 232(%r5)
	ld %r0, 1264(%r6)
	ld %r22, 240(%r6)
	xor %r0, %r0, %r22
	std %r0, 240(%r5)
	ld %r0, 1272(%r6)
	ld %r22, 248(%r6)
	xor %r0, %r0, %r22
	std %r0, 248(%r5)
	ld %r0, 1280(%r6)
	ld %r22, 256(%r6)
	xor %r0, %r0, %r22
	std %r0, 256(%r5)
	ld %r0, 1288(%r6)
	ld %r22, 264(%r6)
	xor %r0, %r0, %r22
	std %r0, 264(%r5)
	ld %r0, 1296(%r6)
	ld %r22, 272(%r6)
	xor %r0, %r0, %r22
	std %r0, 272(%r5)
	ld %r0, 1304(%r6)
	ld %r22, 280(%r6)
	xor %r0, %r0, %r22
	std %r0, 280(%r5)
	ld %r0, 1312(%r6)
	ld %r22, 288(%r6)
	xor %r0, %r0, %r22
	std %r0, 288(%r5)
	ld %r0, 1320(%r6)
	ld %r22, 296(%r6)
	xor %r0, %r0, %r22
	std %r0, 296(%r5)
	ld %r0, 1328(%r6)
	ld %r22, 304(%r6)
	xor %r0, %r0, %r22
	std %r0, 304(%r5)
	ld %r0, 1336(%r6)
	ld %r22, 312(%r6)
	xor %r0, %r0, %r22
	std %r0, 312(%r5)
	ld %r0, 1344(%r6)
	ld %r22, 320(%r6)
	xor %r0, %r0, %r22
	std %r0, 320(%r5)
	ld %r0, 1352(%r6)
	ld %r22, 328(%r6)
	xor %r0, %r0, %r22
	std %r0, 328(%r5)
	ld %r0, 1360(%r6)
	ld %r22, 336(%r6)
	xor %r0, %r0, %r22
	std %r0, 336(%r5)
	ld %r0, 1368(%r6)
	ld %r22, 344(%r6)
	xor %r0, %r0, %r22
	std %r0, 344(%r5)
	ld %r0, 1376(%r6)
	ld %r22, 352(%r6)
	xor %r0, %r0, %r22
	std %r0, 352(%r5)
	ld %r0, 1384(%r6)
	ld %r22, 360(%r6)
	xor %r0, %r0, %r22
	std %r0, 360(%r5)
	ld %r0, 1392(%r6)
	ld %r22, 368(%r6)
	xor %r0, %r0, %r22
	std %r0, 368(%r5)
	ld %r0, 1400(%r6)
	ld %r22, 376(%r6)
	xor %r0, %r0, %r22
	std %r0, 376(%r5)
	ld %r0, 1408(%r6)
	ld %r22, 384(%r6)
	xor %r0, %r0, %r22
	std %r0, 384(%r5)
	ld %r0, 1416(%r6)
	ld %r22, 392(%r6)
	xor %r0, %r0, %r22
	std %r0, 392(%r5)
	ld %r0, 1424(%r6)
	ld %r22, 400(%r6)
	xor %r0, %r0, %r22
	std %r0, 400(%r5)
	ld %r0, 1432(%r6)
	ld %r22, 408(%r6)
	xor %r0, %r0, %r22
	std %r0, 408(%r5)
	ld %r0, 1440(%r6)
	ld %r22, 416(%r6)
	xor %r0, %r0, %r22
	std %r0, 416(%r5)
	ld %r0, 1448(%r6)
	ld %r22, 424(%r6)
	xor %r0, %r0, %r22
	std %r0, 424(%r5)
	ld %r0, 1456(%r6)
	ld %r22, 432(%r6)
	xor %r0, %r0, %r22
	std %r0, 432(%r5)
	ld %r0, 1464(%r6)
	ld %r22, 440(%r6)
	xor %r0, %r0, %r22
	std %r0, 440(%r5)
	ld %r0, 1472(%r6)
	ld %r22, 448(%r6)
	xor %r0, %r0, %r22
	std %r0, 448(%r5)
	ld %r0, 1480(%r6)
	ld %r22, 456(%r6)
	xor %r0, %r0, %r22
	std %r0, 456(%r5)
	ld %r0, 1488(%r6)
	ld %r22, 464(%r6)
	xor %r0, %r0, %r22
	std %r0, 464(%r5)
	ld %r0, 1496(%r6)
	ld %r22, 472(%r6)
	xor %r0, %r0, %r22
	std %r0, 472(%r5)
	ld %r0, 1504(%r6)
	ld %r22, 480(%r6)
	xor %r0, %r0, %r22
	std %r0, 480(%r5)
	ld %r0, 1512(%r6)
	ld %r22, 488(%r6)
	xor %r0, %r0, %r22
	std %r0, 488(%r5)
	ld %r0, 1520(%r6)
	ld %r22, 496(%r6)
	xor %r0, %r0, %r22
	std %r0, 496(%r5)
	ld %r0, 1528(%r6)
	ld %r22, 504(%r6)
	xor %r0, %r0, %r22
	std %r0, 504(%r5)
	ld %r0, 1536(%r6)
	ld %r22, 512(%r6)
	xor %r0, %r0, %r22
	std %r0, 512(%r5)
	ld %r0, 1544(%r6)
	ld %r22, 520(%r6)
	xor %r0, %r0, %r22
	std %r0, 520(%r5)
	ld %r0, 1552(%r6)
	ld %r22, 528(%r6)
	xor %r0, %r0, %r22
	std %r0, 528(%r5)
	ld %r0, 1560(%r6)
	ld %r22, 536(%r6)
	xor %r0, %r0, %r22
	std %r0, 536(%r5)
	ld %r0, 1568(%r6)
	ld %r22, 544(%r6)
	xor %r0, %r0, %r22
	std %r0, 544(%r5)
	ld %r0, 1576(%r6)
	ld %r22, 552(%r6)
	xor %r0, %r0, %r22
	std %r0, 552(%r5)
	ld %r0, 1584(%r6)
	ld %r22, 560(%r6)
	xor %r0, %r0, %r22
	std %r0, 560(%r5)
	ld %r0, 1592(%r6)
	ld %r22, 568(%r6)
	xor %r0, %r0, %r22
	std %r0, 568(%r5)
	ld %r0, 1600(%r6)
	ld %r22, 576(%r6)
	xor %r0, %r0, %r22
	std %r0, 576(%r5)
	ld %r0, 1608(%r6)
	ld %r22, 584(%r6)
	xor %r0, %r0, %r22
	std %r0, 584(%r5)
	ld %r0, 1616(%r6)
	ld %r22, 592(%r6)
	xor %r0, %r0, %r22
	std %r0, 592(%r5)
	ld %r0, 1624(%r6)
	ld %r22, 600(%r6)
	xor %r0, %r0, %r22
	std %r0, 600(%r5)
	ld %r0, 1632(%r6)
	ld %r22, 608(%r6)
	xor %r0, %r0, %r22
	std %r0, 608(%r5)
	ld %r0, 1640(%r6)
	ld %r22, 616(%r6)
	xor %r0, %r0, %r22
	std %r0, 616(%r5)
	ld %r0, 1648(%r6)
	ld %r22, 624(%r6)
	xor %r0, %r0, %r22
	std %r0, 624(%r5)
	ld %r0, 1656(%r6)
	ld %r22, 632(%r6)
	xor %r0, %r0, %r22
	std %r0, 632(%r5)
	ld %r0, 1664(%r6)
	ld %r22, 640(%r6)
	xor %r0, %r0, %r22
	std %r0, 640(%r5)
	ld %r0, 1672(%r6)
	ld %r22, 648(%r6)
	xor %r0, %r0, %r22
	std %r0, 648(%r5)
	ld %r0, 1680(%r6)
	ld %r22, 656(%r6)
	xor %r0, %r0, %r22
	std %r0, 656(%r5)
	ld %r0, 1688(%r6)
	ld %r22, 664(%r6)
	xor %r0, %r0, %r22
	std %r0, 664(%r5)
	ld %r0, 1696(%r6)
	ld %r22, 672(%r6)
	xor %r0, %r0, %r22
	std %r0, 672(%r5)
	ld %r0, 1704(%r6)
	ld %r22, 680(%r6)
	xor %r0, %r0, %r22
	std %r0, 680(%r5)
	ld %r0, 1712(%r6)
	ld %r22, 688(%r6)
	xor %r0, %r0, %r22
	std %r0, 688(%r5)
	ld %r0, 1720(%r6)
	ld %r22, 696(%r6)
	xor %r0, %r0, %r22
	std %r0, 696(%r5)
	ld %r0, 1728(%r6)
	ld %r22, 704(%r6)
	xor %r0, %r0, %r22
	std %r0, 704(%r5)
	ld %r0, 1736(%r6)
	ld %r22, 712(%r6)
	xor %r0, %r0, %r22
	std %r0, 712(%r5)
	ld %r0, 1744(%r6)
	ld %r22, 720(%r6)
	xor %r0, %r0, %r22
	std %r0, 720(%r5)
	ld %r0, 1752(%r6)
	ld %r22, 728(%r6)
	xor %r0, %r0, %r22
	std %r0, 728(%r5)
	ld %r0, 1760(%r6)
	ld %r22, 736(%r6)
	xor %r0, %r0, %r22
	std %r0, 736(%r5)
	ld %r0, 1768(%r6)
	ld %r22, 744(%r6)
	xor %r0, %r0, %r22
	std %r0, 744(%r5)
	ld %r0, 1776(%r6)
	ld %r22, 752(%r6)
	xor %r0, %r0, %r22
	std %r0, 752(%r5)
	ld %r0, 1784(%r6)
	ld %r22, 760(%r6)
	xor %r0, %r0, %r22
	std %r0, 760(%r5)
	ld %r0, 1792(%r6)
	ld %r22, 768(%r6)
	xor %r0, %r0, %r22
	std %r0, 768(%r5)
	ld %r0, 1800(%r6)
	ld %r22, 776(%r6)
	xor %r0, %r0, %r22
	std %r0, 776(%r5)
	ld %r0, 1808(%r6)
	ld %r22, 784(%r6)
	xor %r0, %r0, %r22
	std %r0, 784(%r5)
	ld %r0, 1816(%r6)
	ld %r22, 792(%r6)
	xor %r0, %r0, %r22
	std %r0, 792(%r5)
	ld %r0, 1824(%r6)
	ld %r22, 800(%r6)
	xor %r0, %r0, %r22
	std %r0, 800(%r5)
	ld %r0, 1832(%r6)
	ld %r22, 808(%r6)
	xor %r0, %r0, %r22
	std %r0, 808(%r5)
	ld %r0, 1840(%r6)
	ld %r22, 816(%r6)
	xor %r0, %r0, %r22
	std %r0, 816(%r5)
	ld %r0, 1848(%r6)
	ld %r22, 824(%r6)
	xor %r0, %r0, %r22
	std %r0, 824(%r5)
	ld %r0, 1856(%r6)
	ld %r22, 832(%r6)
	xor %r0, %r0, %r22
	std %r0, 832(%r5)
	ld %r0, 1864(%r6)
	ld %r22, 840(%r6)
	xor %r0, %r0, %r22
	std %r0, 840(%r5)
	ld %r0, 1872(%r6)
	ld %r22, 848(%r6)
	xor %r0, %r0, %r22
	std %r0, 848(%r5)
	ld %r0, 1880(%r6)
	ld %r22, 856(%r6)
	xor %r0, %r0, %r22
	std %r0, 856(%r5)
	ld %r0, 1888(%r6)
	ld %r22, 864(%r6)
	xor %r0, %r0, %r22
	std %r0, 864(%r5)
	ld %r0, 1896(%r6)
	ld %r22, 872(%r6)
	xor %r0, %r0, %r22
	std %r0, 872(%r5)
	ld %r0, 1904(%r6)
	ld %r22, 880(%r6)
	xor %r0, %r0, %r22
	std %r0, 880(%r5)
	ld %r0, 1912(%r6)
	ld %r22, 888(%r6)
	xor %r0, %r0, %r22
	std %r0, 888(%r5)
	ld %r0, 1920(%r6)
	ld %r22, 896(%r6)
	xor %r0, %r0, %r22
	std %r0, 896(%r5)
	ld %r0, 1928(%r6)
	ld %r22, 904(%r6)
	xor %r0, %r0, %r22
	std %r0, 904(%r5)
	ld %r0, 1936(%r6)
	ld %r22, 912(%r6)
	xor %r0, %r0, %r22
	std %r0, 912(%r5)
	ld %r0, 1944(%r6)
	ld %r22, 920(%r6)
	xor %r0, %r0, %r22
	std %r0, 920(%r5)
	ld %r0, 1952(%r6)
	ld %r22, 928(%r6)
	xor %r0, %r0, %r22
	std %r0, 928(%r5)
	ld %r0, 1960(%r6)
	ld %r22, 936(%r6)
	xor %r0, %r0, %r22
	std %r0, 936(%r5)
	ld %r0, 1968(%r6)
	ld %r22, 944(%r6)
	xor %r0, %r0, %r22
	std %r0, 944(%r5)
	ld %r0, 1976(%r6)
	ld %r22, 952(%r6)
	xor %r0, %r0, %r22
	std %r0, 952(%r5)
	ld %r0, 1984(%r6)
	ld %r22, 960(%r6)
	xor %r0, %r0, %r22
	std %r0, 960(%r5)
	ld %r0, 1992(%r6)
	ld %r22, 968(%r6)
	xor %r0, %r0, %r22
	std %r0, 968(%r5)
	ld %r0, 2000(%r6)
	ld %r22, 976(%r6)
	xor %r0, %r0, %r22
	std %r0, 976(%r5)
	ld %r0, 2008(%r6)
	ld %r22, 984(%r6)
	xor %r0, %r0, %r22
	std %r0, 984(%r5)
	ld %r0, 2016(%r6)
	ld %r22, 992(%r6)
	xor %r0, %r0, %r22
	std %r0, 992(%r5)
	ld %r0, 2024(%r6)
	ld %r22, 1000(%r6)
	xor %r0, %r0, %r22
	std %r0, 1000(%r5)
	ld %r0, 2032(%r6)
	ld %r22, 1008(%r6)
	xor %r0, %r0, %r22
	std %r0, 1008(%r5)
	ld %r0, 2040(%r6)
	ld %r22, 1016(%r6)
	xor %r0, %r0, %r22
	std %r0, 1016(%r5)
	ld %r14, 2048(%r6)
	ld %r15, 2056(%r6)
	ld %r16, 2064(%r6)
	ld %r17, 2072(%r6)
	ld %r18, 2080(%r6)
	ld %r19, 2088(%r6)
	ld %r20, 2096(%r6)
	ld %r21, 2104(%r6)
	ld %r22, 2112(%r6)
	blr

vg_argon2_hprime:
	std %r27, 840(%r7)
	std %r28, 848(%r7)
	std %r29, 856(%r7)
	std %r30, 864(%r7)
	std %r31, 872(%r7)
	mflr %r0
	std %r0, 880(%r7)
	addi %r31, %r7, 0
	addi %r27, %r3, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	stw %r6, 832(%r31)
	addi %r4, %r30, 0
	addi %r10, %r4, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 20f
	li %r4, 64
	b 21f
20:
21:
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 832
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 4
	addi %r5, %r27, 0
	addi %r6, %r28, 0
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	addi %r4, %r28, 4
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 22f
	li %r9, 32
	addi %r5, %r31, 768
24:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 24b
	addi %r30, %r30, -32
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 25f
27:
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 768
	li %r6, 64
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	li %r9, 32
	addi %r5, %r31, 768
28:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 28b
	addi %r30, %r30, -32
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	beq %cr0, 27b
	b 26f
25:
26:
	addi %r4, %r30, 0
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 768
	li %r6, 64
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	b 23f
22:
23:
	addi %r9, %r30, 0
	addi %r5, %r31, 768
29:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 29b
	ld %r0, 880(%r31)
	mtlr %r0
	ld %r27, 840(%r31)
	ld %r28, 848(%r31)
	ld %r29, 856(%r31)
	ld %r30, 864(%r31)
	ld %r31, 872(%r31)
	blr

vg_argon2:
	stdu %r1, -336(%r1)
	addi %r12, %r1, 0
	mflr %r0
	std %r0, 104(%r12)
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	std %r3, 144(%r12)
	std %r4, 152(%r12)
	std %r5, 160(%r12)
	std %r6, 168(%r12)
	std %r7, 176(%r12)
	std %r8, 184(%r12)
	std %r9, 192(%r12)
	std %r10, 200(%r12)
	addi %r30, %r12, 0
	ld %r31, 488(%r30)
	lwz %r3, 200(%r30)
	rldicr %r5, %r3, 2, 61
	lwz %r4, 192(%r30)
	li %r6, 0
	li %r7, 0
	li %r9, 1
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	std %r6, 264(%r30)
	rldicr %r6, %r6, 2, 61
	std %r6, 248(%r30)
	rldicr %r6, %r6, 10, 53
	std %r6, 256(%r30)
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	lwz %r3, 200(%r30)
	stw %r3, 896(%r31)
	lwz %r3, 504(%r30)
	stw %r3, 900(%r31)
	lwz %r3, 192(%r30)
	stw %r3, 904(%r31)
	lwz %r3, 184(%r30)
	stw %r3, 908(%r31)
	li %r3, 19
	stw %r3, 912(%r31)
	lwz %r3, 144(%r30)
	stw %r3, 916(%r31)
	li %r4, 0
	addi %r5, %r31, 896
	li %r6, 24
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r3, 24
	std %r3, 272(%r30)
	ld %r3, 160(%r30)
	stw %r3, 920(%r31)
	ld %r4, 272(%r30)
	addi %r5, %r31, 920
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	addi %r4, %r4, 4
	std %r4, 272(%r30)
	ld %r5, 152(%r30)
	ld %r6, 160(%r30)
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	ld %r3, 160(%r30)
	add %r4, %r4, %r3
	std %r4, 272(%r30)
	ld %r3, 176(%r30)
	stw %r3, 920(%r31)
	ld %r4, 272(%r30)
	addi %r5, %r31, 920
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	addi %r4, %r4, 4
	std %r4, 272(%r30)
	ld %r5, 168(%r30)
	ld %r6, 176(%r30)
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	ld %r3, 176(%r30)
	add %r4, %r4, %r3
	std %r4, 272(%r30)
	ld %r3, 448(%r30)
	stw %r3, 920(%r31)
	ld %r4, 272(%r30)
	addi %r5, %r31, 920
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	addi %r4, %r4, 4
	std %r4, 272(%r30)
	ld %r5, 440(%r30)
	ld %r6, 448(%r30)
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	ld %r3, 448(%r30)
	add %r4, %r4, %r3
	std %r4, 272(%r30)
	ld %r3, 464(%r30)
	stw %r3, 920(%r31)
	ld %r4, 272(%r30)
	addi %r5, %r31, 920
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	addi %r4, %r4, 4
	std %r4, 272(%r30)
	ld %r5, 456(%r30)
	ld %r6, 464(%r30)
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	ld %r4, 272(%r30)
	ld %r3, 464(%r30)
	add %r4, %r4, %r3
	std %r4, 272(%r30)
	ld %r4, 272(%r30)
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	ld %r3, 768(%r31)
	std %r3, 32(%r30)
	ld %r3, 776(%r31)
	std %r3, 40(%r30)
	ld %r3, 784(%r31)
	std %r3, 48(%r30)
	ld %r3, 792(%r31)
	std %r3, 56(%r30)
	ld %r3, 800(%r31)
	std %r3, 64(%r30)
	ld %r3, 808(%r31)
	std %r3, 72(%r30)
	ld %r3, 816(%r31)
	std %r3, 80(%r30)
	ld %r3, 824(%r31)
	std %r3, 88(%r30)
	ld %r5, 472(%r30)
	ld %r6, 480(%r30)
	rldicr %r6, %r6, 7, 56
	li %r7, 0
20:
	std %r7, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	ld %r29, 472(%r30)
	li %r28, 0
21:
	li %r3, 0
	stw %r3, 96(%r30)
	stw %r28, 100(%r30)
	addi %r3, %r30, 32
	li %r4, 72
	addi %r5, %r29, 0
	li %r6, 1024
	addi %r7, %r31, 0
	bl {vg_argon2_hprime}
	addi %r29, %r29, 1024
	li %r3, 1
	stw %r3, 96(%r30)
	stw %r28, 100(%r30)
	addi %r3, %r30, 32
	li %r4, 72
	addi %r5, %r29, 0
	li %r6, 1024
	addi %r7, %r31, 0
	bl {vg_argon2_hprime}
	ld %r3, 256(%r30)
	add %r29, %r29, %r3
	addi %r29, %r29, -1024
	addi %r28, %r28, 1
	lwz %r3, 200(%r30)
	subf %r3, %r3, %r28
	cmpldi %cr0, %r3, 0
	bne %cr0, 21b
	li %r3, 0
	std %r3, 208(%r30)
22:
	li %r3, 0
	std %r3, 224(%r30)
23:
	li %r3, 0
	std %r3, 216(%r30)
24:
	li %r3, 0
	std %r3, 240(%r30)
	ld %r3, 208(%r30)
	ld %r4, 224(%r30)
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 25f
	li %r3, 0
	std %r3, 232(%r30)
	b 26f
25:
	li %r3, 2
	std %r3, 232(%r30)
26:
	ld %r3, 232(%r30)
	ld %r4, 264(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	beq %cr0, 27f
29:
	lwz %r3, 144(%r30)
	li %r4, 1
	xor %r4, %r3, %r4
	li %r5, 2
	xor %r5, %r3, %r5
	ld %r6, 208(%r30)
	or %r5, %r5, %r6
	ld %r6, 224(%r30)
	rldicl %r6, %r6, 63, 1
	or %r5, %r5, %r6
	li %r7, 0
	subf %r7, %r4, %r7
	or %r7, %r7, %r4
	rldicl %r8, %r7, 1, 63
	li %r7, 0
	subf %r7, %r5, %r7
	or %r7, %r7, %r5
	rldicl %r6, %r7, 1, 63
	and %r8, %r8, %r6
	cmpldi %cr0, %r8, 0
	bne %cr0, 210f
	ld %r3, 232(%r30)
	rldicl %r3, %r3, 57, 7
	addi %r3, %r3, 1
	ld %r4, 240(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	beq %cr0, 212f
	std %r3, 240(%r30)
	li %r3, 0
	std %r3, 5120(%r31)
	std %r3, 5128(%r31)
	std %r3, 5136(%r31)
	std %r3, 5144(%r31)
	std %r3, 5152(%r31)
	std %r3, 5160(%r31)
	std %r3, 5168(%r31)
	std %r3, 5176(%r31)
	std %r3, 5184(%r31)
	std %r3, 5192(%r31)
	std %r3, 5200(%r31)
	std %r3, 5208(%r31)
	std %r3, 5216(%r31)
	std %r3, 5224(%r31)
	std %r3, 5232(%r31)
	std %r3, 5240(%r31)
	std %r3, 5248(%r31)
	std %r3, 5256(%r31)
	std %r3, 5264(%r31)
	std %r3, 5272(%r31)
	std %r3, 5280(%r31)
	std %r3, 5288(%r31)
	std %r3, 5296(%r31)
	std %r3, 5304(%r31)
	std %r3, 5312(%r31)
	std %r3, 5320(%r31)
	std %r3, 5328(%r31)
	std %r3, 5336(%r31)
	std %r3, 5344(%r31)
	std %r3, 5352(%r31)
	std %r3, 5360(%r31)
	std %r3, 5368(%r31)
	std %r3, 5376(%r31)
	std %r3, 5384(%r31)
	std %r3, 5392(%r31)
	std %r3, 5400(%r31)
	std %r3, 5408(%r31)
	std %r3, 5416(%r31)
	std %r3, 5424(%r31)
	std %r3, 5432(%r31)
	std %r3, 5440(%r31)
	std %r3, 5448(%r31)
	std %r3, 5456(%r31)
	std %r3, 5464(%r31)
	std %r3, 5472(%r31)
	std %r3, 5480(%r31)
	std %r3, 5488(%r31)
	std %r3, 5496(%r31)
	std %r3, 5504(%r31)
	std %r3, 5512(%r31)
	std %r3, 5520(%r31)
	std %r3, 5528(%r31)
	std %r3, 5536(%r31)
	std %r3, 5544(%r31)
	std %r3, 5552(%r31)
	std %r3, 5560(%r31)
	std %r3, 5568(%r31)
	std %r3, 5576(%r31)
	std %r3, 5584(%r31)
	std %r3, 5592(%r31)
	std %r3, 5600(%r31)
	std %r3, 5608(%r31)
	std %r3, 5616(%r31)
	std %r3, 5624(%r31)
	std %r3, 5632(%r31)
	std %r3, 5640(%r31)
	std %r3, 5648(%r31)
	std %r3, 5656(%r31)
	std %r3, 5664(%r31)
	std %r3, 5672(%r31)
	std %r3, 5680(%r31)
	std %r3, 5688(%r31)
	std %r3, 5696(%r31)
	std %r3, 5704(%r31)
	std %r3, 5712(%r31)
	std %r3, 5720(%r31)
	std %r3, 5728(%r31)
	std %r3, 5736(%r31)
	std %r3, 5744(%r31)
	std %r3, 5752(%r31)
	std %r3, 5760(%r31)
	std %r3, 5768(%r31)
	std %r3, 5776(%r31)
	std %r3, 5784(%r31)
	std %r3, 5792(%r31)
	std %r3, 5800(%r31)
	std %r3, 5808(%r31)
	std %r3, 5816(%r31)
	std %r3, 5824(%r31)
	std %r3, 5832(%r31)
	std %r3, 5840(%r31)
	std %r3, 5848(%r31)
	std %r3, 5856(%r31)
	std %r3, 5864(%r31)
	std %r3, 5872(%r31)
	std %r3, 5880(%r31)
	std %r3, 5888(%r31)
	std %r3, 5896(%r31)
	std %r3, 5904(%r31)
	std %r3, 5912(%r31)
	std %r3, 5920(%r31)
	std %r3, 5928(%r31)
	std %r3, 5936(%r31)
	std %r3, 5944(%r31)
	std %r3, 5952(%r31)
	std %r3, 5960(%r31)
	std %r3, 5968(%r31)
	std %r3, 5976(%r31)
	std %r3, 5984(%r31)
	std %r3, 5992(%r31)
	std %r3, 6000(%r31)
	std %r3, 6008(%r31)
	std %r3, 6016(%r31)
	std %r3, 6024(%r31)
	std %r3, 6032(%r31)
	std %r3, 6040(%r31)
	std %r3, 6048(%r31)
	std %r3, 6056(%r31)
	std %r3, 6064(%r31)
	std %r3, 6072(%r31)
	std %r3, 6080(%r31)
	std %r3, 6088(%r31)
	std %r3, 6096(%r31)
	std %r3, 6104(%r31)
	std %r3, 6112(%r31)
	std %r3, 6120(%r31)
	std %r3, 6128(%r31)
	std %r3, 6136(%r31)
	li %r3, 0
	std %r3, 7168(%r31)
	std %r3, 7176(%r31)
	std %r3, 7184(%r31)
	std %r3, 7192(%r31)
	std %r3, 7200(%r31)
	std %r3, 7208(%r31)
	std %r3, 7216(%r31)
	std %r3, 7224(%r31)
	std %r3, 7232(%r31)
	std %r3, 7240(%r31)
	std %r3, 7248(%r31)
	std %r3, 7256(%r31)
	std %r3, 7264(%r31)
	std %r3, 7272(%r31)
	std %r3, 7280(%r31)
	std %r3, 7288(%r31)
	std %r3, 7296(%r31)
	std %r3, 7304(%r31)
	std %r3, 7312(%r31)
	std %r3, 7320(%r31)
	std %r3, 7328(%r31)
	std %r3, 7336(%r31)
	std %r3, 7344(%r31)
	std %r3, 7352(%r31)
	std %r3, 7360(%r31)
	std %r3, 7368(%r31)
	std %r3, 7376(%r31)
	std %r3, 7384(%r31)
	std %r3, 7392(%r31)
	std %r3, 7400(%r31)
	std %r3, 7408(%r31)
	std %r3, 7416(%r31)
	std %r3, 7424(%r31)
	std %r3, 7432(%r31)
	std %r3, 7440(%r31)
	std %r3, 7448(%r31)
	std %r3, 7456(%r31)
	std %r3, 7464(%r31)
	std %r3, 7472(%r31)
	std %r3, 7480(%r31)
	std %r3, 7488(%r31)
	std %r3, 7496(%r31)
	std %r3, 7504(%r31)
	std %r3, 7512(%r31)
	std %r3, 7520(%r31)
	std %r3, 7528(%r31)
	std %r3, 7536(%r31)
	std %r3, 7544(%r31)
	std %r3, 7552(%r31)
	std %r3, 7560(%r31)
	std %r3, 7568(%r31)
	std %r3, 7576(%r31)
	std %r3, 7584(%r31)
	std %r3, 7592(%r31)
	std %r3, 7600(%r31)
	std %r3, 7608(%r31)
	std %r3, 7616(%r31)
	std %r3, 7624(%r31)
	std %r3, 7632(%r31)
	std %r3, 7640(%r31)
	std %r3, 7648(%r31)
	std %r3, 7656(%r31)
	std %r3, 7664(%r31)
	std %r3, 7672(%r31)
	std %r3, 7680(%r31)
	std %r3, 7688(%r31)
	std %r3, 7696(%r31)
	std %r3, 7704(%r31)
	std %r3, 7712(%r31)
	std %r3, 7720(%r31)
	std %r3, 7728(%r31)
	std %r3, 7736(%r31)
	std %r3, 7744(%r31)
	std %r3, 7752(%r31)
	std %r3, 7760(%r31)
	std %r3, 7768(%r31)
	std %r3, 7776(%r31)
	std %r3, 7784(%r31)
	std %r3, 7792(%r31)
	std %r3, 7800(%r31)
	std %r3, 7808(%r31)
	std %r3, 7816(%r31)
	std %r3, 7824(%r31)
	std %r3, 7832(%r31)
	std %r3, 7840(%r31)
	std %r3, 7848(%r31)
	std %r3, 7856(%r31)
	std %r3, 7864(%r31)
	std %r3, 7872(%r31)
	std %r3, 7880(%r31)
	std %r3, 7888(%r31)
	std %r3, 7896(%r31)
	std %r3, 7904(%r31)
	std %r3, 7912(%r31)
	std %r3, 7920(%r31)
	std %r3, 7928(%r31)
	std %r3, 7936(%r31)
	std %r3, 7944(%r31)
	std %r3, 7952(%r31)
	std %r3, 7960(%r31)
	std %r3, 7968(%r31)
	std %r3, 7976(%r31)
	std %r3, 7984(%r31)
	std %r3, 7992(%r31)
	std %r3, 8000(%r31)
	std %r3, 8008(%r31)
	std %r3, 8016(%r31)
	std %r3, 8024(%r31)
	std %r3, 8032(%r31)
	std %r3, 8040(%r31)
	std %r3, 8048(%r31)
	std %r3, 8056(%r31)
	std %r3, 8064(%r31)
	std %r3, 8072(%r31)
	std %r3, 8080(%r31)
	std %r3, 8088(%r31)
	std %r3, 8096(%r31)
	std %r3, 8104(%r31)
	std %r3, 8112(%r31)
	std %r3, 8120(%r31)
	std %r3, 8128(%r31)
	std %r3, 8136(%r31)
	std %r3, 8144(%r31)
	std %r3, 8152(%r31)
	std %r3, 8160(%r31)
	std %r3, 8168(%r31)
	std %r3, 8176(%r31)
	std %r3, 8184(%r31)
	ld %r3, 208(%r30)
	std %r3, 5120(%r31)
	ld %r3, 216(%r30)
	std %r3, 5128(%r31)
	ld %r3, 224(%r30)
	std %r3, 5136(%r31)
	ld %r3, 480(%r30)
	std %r3, 5144(%r31)
	lwz %r3, 184(%r30)
	std %r3, 5152(%r31)
	lwz %r3, 144(%r30)
	std %r3, 5160(%r31)
	ld %r3, 240(%r30)
	std %r3, 5168(%r31)
	addi %r3, %r31, 7168
	addi %r4, %r31, 5120
	addi %r5, %r31, 4096
	addi %r6, %r31, 0
	bl {vg_argon2_compress}
	addi %r3, %r31, 7168
	addi %r4, %r31, 4096
	addi %r5, %r31, 6144
	addi %r6, %r31, 0
	bl {vg_argon2_compress}
	b 213f
212:
213:
	ld %r3, 232(%r30)
	li %r4, 127
	and %r3, %r3, %r4
	rldicr %r3, %r3, 3, 60
	add %r3, %r31, %r3
	lwz %r4, 6144(%r3)
	std %r4, 280(%r30)
	lwz %r4, 6148(%r3)
	std %r4, 288(%r30)
	b 211f
210:
	ld %r3, 224(%r30)
	ld %r5, 264(%r30)
	mulld %r3, %r3, %r5
	ld %r5, 232(%r30)
	add %r4, %r3, %r5
	cmpldi %cr0, %r4, 0
	beq %cr0, 214f
	b 215f
214:
	ld %r4, 248(%r30)
215:
	addi %r4, %r4, -1
	ld %r3, 216(%r30)
	ld %r5, 248(%r30)
	mulld %r3, %r3, %r5
	add %r3, %r3, %r4
	rldicr %r3, %r3, 10, 53
	ld %r5, 472(%r30)
	add %r3, %r5, %r3
	lwz %r4, 0(%r3)
	std %r4, 280(%r30)
	lwz %r4, 4(%r3)
	std %r4, 288(%r30)
211:
	ld %r4, 288(%r30)
	lwz %r5, 200(%r30)
	li %r6, 0
	li %r7, 0
	li %r9, 1
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	rlwinm %r8, %r4, 1, 31, 31
	rldicr %r4, %r4, 1, 62
	rldicr %r7, %r7, 1, 62
	add %r7, %r7, %r8
	subf %r8, %r5, %r7
	rldicl %r8, %r8, 1, 63
	subf %r8, %r8, %r9
	rldicr %r6, %r6, 1, 62
	add %r6, %r6, %r8
	mulld %r8, %r8, %r5
	subf %r7, %r8, %r7
	std %r7, 296(%r30)
	ld %r3, 208(%r30)
	ld %r4, 224(%r30)
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
	b 217f
216:
	ld %r3, 216(%r30)
	std %r3, 296(%r30)
217:
	li %r3, 0
	std %r3, 304(%r30)
	ld %r4, 208(%r30)
	cmpldi %cr0, %r4, 0
	beq %cr0, 218f
	ld %r4, 224(%r30)
	addi %r4, %r4, -3
	cmpldi %cr0, %r4, 0
	beq %cr0, 220f
	ld %r3, 224(%r30)
	addi %r3, %r3, 1
	ld %r5, 264(%r30)
	mulld %r3, %r3, %r5
	std %r3, 304(%r30)
	b 221f
220:
221:
	b 219f
218:
219:
	ld %r4, 208(%r30)
	cmpldi %cr0, %r4, 0
	beq %cr0, 222f
	ld %r3, 248(%r30)
	ld %r5, 264(%r30)
	subf %r3, %r5, %r3
	b 223f
222:
	ld %r3, 224(%r30)
	ld %r5, 264(%r30)
	mulld %r3, %r3, %r5
223:
	ld %r5, 232(%r30)
	add %r4, %r3, %r5
	addi %r4, %r4, -1
	li %r6, 0
	subf %r6, %r5, %r6
	or %r6, %r6, %r5
	rldicl %r6, %r6, 1, 63
	addi %r6, %r6, -1
	add %r3, %r3, %r6
	ld %r5, 296(%r30)
	ld %r6, 216(%r30)
	xor %r5, %r5, %r6
	li %r6, 0
	subf %r6, %r5, %r6
	or %r6, %r6, %r5
	rldicl %r6, %r6, 1, 63
	addi %r5, %r6, -1
	xor %r4, %r4, %r3
	and %r4, %r4, %r5
	xor %r3, %r3, %r4
	std %r3, 320(%r30)
	ld %r4, 280(%r30)
	mulld %r4, %r4, %r4
	rldicl %r4, %r4, 32, 32
	ld %r5, 320(%r30)
	mulld %r4, %r5, %r4
	rldicl %r4, %r4, 32, 32
	addi %r3, %r5, -1
	subf %r3, %r4, %r3
	ld %r4, 304(%r30)
	add %r3, %r3, %r4
	ld %r4, 248(%r30)
	subf %r5, %r4, %r3
	rldicl %r6, %r5, 1, 63
	mulld %r6, %r6, %r4
	add %r3, %r5, %r6
	addi %r4, %r3, 0
	ld %r3, 296(%r30)
	ld %r5, 248(%r30)
	mulld %r3, %r3, %r5
	add %r3, %r3, %r4
	rldicr %r3, %r3, 10, 53
	ld %r5, 472(%r30)
	add %r3, %r5, %r3
	std %r3, 328(%r30)
	ld %r3, 224(%r30)
	ld %r5, 264(%r30)
	mulld %r3, %r3, %r5
	ld %r5, 232(%r30)
	add %r4, %r3, %r5
	ld %r3, 216(%r30)
	ld %r5, 248(%r30)
	mulld %r3, %r3, %r5
	add %r3, %r3, %r4
	rldicr %r3, %r3, 10, 53
	ld %r5, 472(%r30)
	add %r3, %r5, %r3
	std %r3, 312(%r30)
	ld %r3, 224(%r30)
	ld %r5, 264(%r30)
	mulld %r3, %r3, %r5
	ld %r5, 232(%r30)
	add %r4, %r3, %r5
	cmpldi %cr0, %r4, 0
	beq %cr0, 224f
	b 225f
224:
	ld %r4, 248(%r30)
225:
	addi %r4, %r4, -1
	ld %r3, 216(%r30)
	ld %r5, 248(%r30)
	mulld %r3, %r3, %r5
	add %r3, %r3, %r4
	rldicr %r3, %r3, 10, 53
	ld %r5, 472(%r30)
	add %r3, %r5, %r3
	ld %r4, 328(%r30)
	addi %r5, %r31, 4096
	addi %r6, %r31, 0
	bl {vg_argon2_compress}
	addi %r4, %r31, 4096
	ld %r6, 312(%r30)
	ld %r3, 208(%r30)
	cmpldi %cr0, %r3, 0
	beq %cr0, 226f
	ld %r3, 0(%r4)
	ld %r5, 0(%r6)
	xor %r3, %r3, %r5
	std %r3, 0(%r6)
	ld %r3, 8(%r4)
	ld %r5, 8(%r6)
	xor %r3, %r3, %r5
	std %r3, 8(%r6)
	ld %r3, 16(%r4)
	ld %r5, 16(%r6)
	xor %r3, %r3, %r5
	std %r3, 16(%r6)
	ld %r3, 24(%r4)
	ld %r5, 24(%r6)
	xor %r3, %r3, %r5
	std %r3, 24(%r6)
	ld %r3, 32(%r4)
	ld %r5, 32(%r6)
	xor %r3, %r3, %r5
	std %r3, 32(%r6)
	ld %r3, 40(%r4)
	ld %r5, 40(%r6)
	xor %r3, %r3, %r5
	std %r3, 40(%r6)
	ld %r3, 48(%r4)
	ld %r5, 48(%r6)
	xor %r3, %r3, %r5
	std %r3, 48(%r6)
	ld %r3, 56(%r4)
	ld %r5, 56(%r6)
	xor %r3, %r3, %r5
	std %r3, 56(%r6)
	ld %r3, 64(%r4)
	ld %r5, 64(%r6)
	xor %r3, %r3, %r5
	std %r3, 64(%r6)
	ld %r3, 72(%r4)
	ld %r5, 72(%r6)
	xor %r3, %r3, %r5
	std %r3, 72(%r6)
	ld %r3, 80(%r4)
	ld %r5, 80(%r6)
	xor %r3, %r3, %r5
	std %r3, 80(%r6)
	ld %r3, 88(%r4)
	ld %r5, 88(%r6)
	xor %r3, %r3, %r5
	std %r3, 88(%r6)
	ld %r3, 96(%r4)
	ld %r5, 96(%r6)
	xor %r3, %r3, %r5
	std %r3, 96(%r6)
	ld %r3, 104(%r4)
	ld %r5, 104(%r6)
	xor %r3, %r3, %r5
	std %r3, 104(%r6)
	ld %r3, 112(%r4)
	ld %r5, 112(%r6)
	xor %r3, %r3, %r5
	std %r3, 112(%r6)
	ld %r3, 120(%r4)
	ld %r5, 120(%r6)
	xor %r3, %r3, %r5
	std %r3, 120(%r6)
	ld %r3, 128(%r4)
	ld %r5, 128(%r6)
	xor %r3, %r3, %r5
	std %r3, 128(%r6)
	ld %r3, 136(%r4)
	ld %r5, 136(%r6)
	xor %r3, %r3, %r5
	std %r3, 136(%r6)
	ld %r3, 144(%r4)
	ld %r5, 144(%r6)
	xor %r3, %r3, %r5
	std %r3, 144(%r6)
	ld %r3, 152(%r4)
	ld %r5, 152(%r6)
	xor %r3, %r3, %r5
	std %r3, 152(%r6)
	ld %r3, 160(%r4)
	ld %r5, 160(%r6)
	xor %r3, %r3, %r5
	std %r3, 160(%r6)
	ld %r3, 168(%r4)
	ld %r5, 168(%r6)
	xor %r3, %r3, %r5
	std %r3, 168(%r6)
	ld %r3, 176(%r4)
	ld %r5, 176(%r6)
	xor %r3, %r3, %r5
	std %r3, 176(%r6)
	ld %r3, 184(%r4)
	ld %r5, 184(%r6)
	xor %r3, %r3, %r5
	std %r3, 184(%r6)
	ld %r3, 192(%r4)
	ld %r5, 192(%r6)
	xor %r3, %r3, %r5
	std %r3, 192(%r6)
	ld %r3, 200(%r4)
	ld %r5, 200(%r6)
	xor %r3, %r3, %r5
	std %r3, 200(%r6)
	ld %r3, 208(%r4)
	ld %r5, 208(%r6)
	xor %r3, %r3, %r5
	std %r3, 208(%r6)
	ld %r3, 216(%r4)
	ld %r5, 216(%r6)
	xor %r3, %r3, %r5
	std %r3, 216(%r6)
	ld %r3, 224(%r4)
	ld %r5, 224(%r6)
	xor %r3, %r3, %r5
	std %r3, 224(%r6)
	ld %r3, 232(%r4)
	ld %r5, 232(%r6)
	xor %r3, %r3, %r5
	std %r3, 232(%r6)
	ld %r3, 240(%r4)
	ld %r5, 240(%r6)
	xor %r3, %r3, %r5
	std %r3, 240(%r6)
	ld %r3, 248(%r4)
	ld %r5, 248(%r6)
	xor %r3, %r3, %r5
	std %r3, 248(%r6)
	ld %r3, 256(%r4)
	ld %r5, 256(%r6)
	xor %r3, %r3, %r5
	std %r3, 256(%r6)
	ld %r3, 264(%r4)
	ld %r5, 264(%r6)
	xor %r3, %r3, %r5
	std %r3, 264(%r6)
	ld %r3, 272(%r4)
	ld %r5, 272(%r6)
	xor %r3, %r3, %r5
	std %r3, 272(%r6)
	ld %r3, 280(%r4)
	ld %r5, 280(%r6)
	xor %r3, %r3, %r5
	std %r3, 280(%r6)
	ld %r3, 288(%r4)
	ld %r5, 288(%r6)
	xor %r3, %r3, %r5
	std %r3, 288(%r6)
	ld %r3, 296(%r4)
	ld %r5, 296(%r6)
	xor %r3, %r3, %r5
	std %r3, 296(%r6)
	ld %r3, 304(%r4)
	ld %r5, 304(%r6)
	xor %r3, %r3, %r5
	std %r3, 304(%r6)
	ld %r3, 312(%r4)
	ld %r5, 312(%r6)
	xor %r3, %r3, %r5
	std %r3, 312(%r6)
	ld %r3, 320(%r4)
	ld %r5, 320(%r6)
	xor %r3, %r3, %r5
	std %r3, 320(%r6)
	ld %r3, 328(%r4)
	ld %r5, 328(%r6)
	xor %r3, %r3, %r5
	std %r3, 328(%r6)
	ld %r3, 336(%r4)
	ld %r5, 336(%r6)
	xor %r3, %r3, %r5
	std %r3, 336(%r6)
	ld %r3, 344(%r4)
	ld %r5, 344(%r6)
	xor %r3, %r3, %r5
	std %r3, 344(%r6)
	ld %r3, 352(%r4)
	ld %r5, 352(%r6)
	xor %r3, %r3, %r5
	std %r3, 352(%r6)
	ld %r3, 360(%r4)
	ld %r5, 360(%r6)
	xor %r3, %r3, %r5
	std %r3, 360(%r6)
	ld %r3, 368(%r4)
	ld %r5, 368(%r6)
	xor %r3, %r3, %r5
	std %r3, 368(%r6)
	ld %r3, 376(%r4)
	ld %r5, 376(%r6)
	xor %r3, %r3, %r5
	std %r3, 376(%r6)
	ld %r3, 384(%r4)
	ld %r5, 384(%r6)
	xor %r3, %r3, %r5
	std %r3, 384(%r6)
	ld %r3, 392(%r4)
	ld %r5, 392(%r6)
	xor %r3, %r3, %r5
	std %r3, 392(%r6)
	ld %r3, 400(%r4)
	ld %r5, 400(%r6)
	xor %r3, %r3, %r5
	std %r3, 400(%r6)
	ld %r3, 408(%r4)
	ld %r5, 408(%r6)
	xor %r3, %r3, %r5
	std %r3, 408(%r6)
	ld %r3, 416(%r4)
	ld %r5, 416(%r6)
	xor %r3, %r3, %r5
	std %r3, 416(%r6)
	ld %r3, 424(%r4)
	ld %r5, 424(%r6)
	xor %r3, %r3, %r5
	std %r3, 424(%r6)
	ld %r3, 432(%r4)
	ld %r5, 432(%r6)
	xor %r3, %r3, %r5
	std %r3, 432(%r6)
	ld %r3, 440(%r4)
	ld %r5, 440(%r6)
	xor %r3, %r3, %r5
	std %r3, 440(%r6)
	ld %r3, 448(%r4)
	ld %r5, 448(%r6)
	xor %r3, %r3, %r5
	std %r3, 448(%r6)
	ld %r3, 456(%r4)
	ld %r5, 456(%r6)
	xor %r3, %r3, %r5
	std %r3, 456(%r6)
	ld %r3, 464(%r4)
	ld %r5, 464(%r6)
	xor %r3, %r3, %r5
	std %r3, 464(%r6)
	ld %r3, 472(%r4)
	ld %r5, 472(%r6)
	xor %r3, %r3, %r5
	std %r3, 472(%r6)
	ld %r3, 480(%r4)
	ld %r5, 480(%r6)
	xor %r3, %r3, %r5
	std %r3, 480(%r6)
	ld %r3, 488(%r4)
	ld %r5, 488(%r6)
	xor %r3, %r3, %r5
	std %r3, 488(%r6)
	ld %r3, 496(%r4)
	ld %r5, 496(%r6)
	xor %r3, %r3, %r5
	std %r3, 496(%r6)
	ld %r3, 504(%r4)
	ld %r5, 504(%r6)
	xor %r3, %r3, %r5
	std %r3, 504(%r6)
	ld %r3, 512(%r4)
	ld %r5, 512(%r6)
	xor %r3, %r3, %r5
	std %r3, 512(%r6)
	ld %r3, 520(%r4)
	ld %r5, 520(%r6)
	xor %r3, %r3, %r5
	std %r3, 520(%r6)
	ld %r3, 528(%r4)
	ld %r5, 528(%r6)
	xor %r3, %r3, %r5
	std %r3, 528(%r6)
	ld %r3, 536(%r4)
	ld %r5, 536(%r6)
	xor %r3, %r3, %r5
	std %r3, 536(%r6)
	ld %r3, 544(%r4)
	ld %r5, 544(%r6)
	xor %r3, %r3, %r5
	std %r3, 544(%r6)
	ld %r3, 552(%r4)
	ld %r5, 552(%r6)
	xor %r3, %r3, %r5
	std %r3, 552(%r6)
	ld %r3, 560(%r4)
	ld %r5, 560(%r6)
	xor %r3, %r3, %r5
	std %r3, 560(%r6)
	ld %r3, 568(%r4)
	ld %r5, 568(%r6)
	xor %r3, %r3, %r5
	std %r3, 568(%r6)
	ld %r3, 576(%r4)
	ld %r5, 576(%r6)
	xor %r3, %r3, %r5
	std %r3, 576(%r6)
	ld %r3, 584(%r4)
	ld %r5, 584(%r6)
	xor %r3, %r3, %r5
	std %r3, 584(%r6)
	ld %r3, 592(%r4)
	ld %r5, 592(%r6)
	xor %r3, %r3, %r5
	std %r3, 592(%r6)
	ld %r3, 600(%r4)
	ld %r5, 600(%r6)
	xor %r3, %r3, %r5
	std %r3, 600(%r6)
	ld %r3, 608(%r4)
	ld %r5, 608(%r6)
	xor %r3, %r3, %r5
	std %r3, 608(%r6)
	ld %r3, 616(%r4)
	ld %r5, 616(%r6)
	xor %r3, %r3, %r5
	std %r3, 616(%r6)
	ld %r3, 624(%r4)
	ld %r5, 624(%r6)
	xor %r3, %r3, %r5
	std %r3, 624(%r6)
	ld %r3, 632(%r4)
	ld %r5, 632(%r6)
	xor %r3, %r3, %r5
	std %r3, 632(%r6)
	ld %r3, 640(%r4)
	ld %r5, 640(%r6)
	xor %r3, %r3, %r5
	std %r3, 640(%r6)
	ld %r3, 648(%r4)
	ld %r5, 648(%r6)
	xor %r3, %r3, %r5
	std %r3, 648(%r6)
	ld %r3, 656(%r4)
	ld %r5, 656(%r6)
	xor %r3, %r3, %r5
	std %r3, 656(%r6)
	ld %r3, 664(%r4)
	ld %r5, 664(%r6)
	xor %r3, %r3, %r5
	std %r3, 664(%r6)
	ld %r3, 672(%r4)
	ld %r5, 672(%r6)
	xor %r3, %r3, %r5
	std %r3, 672(%r6)
	ld %r3, 680(%r4)
	ld %r5, 680(%r6)
	xor %r3, %r3, %r5
	std %r3, 680(%r6)
	ld %r3, 688(%r4)
	ld %r5, 688(%r6)
	xor %r3, %r3, %r5
	std %r3, 688(%r6)
	ld %r3, 696(%r4)
	ld %r5, 696(%r6)
	xor %r3, %r3, %r5
	std %r3, 696(%r6)
	ld %r3, 704(%r4)
	ld %r5, 704(%r6)
	xor %r3, %r3, %r5
	std %r3, 704(%r6)
	ld %r3, 712(%r4)
	ld %r5, 712(%r6)
	xor %r3, %r3, %r5
	std %r3, 712(%r6)
	ld %r3, 720(%r4)
	ld %r5, 720(%r6)
	xor %r3, %r3, %r5
	std %r3, 720(%r6)
	ld %r3, 728(%r4)
	ld %r5, 728(%r6)
	xor %r3, %r3, %r5
	std %r3, 728(%r6)
	ld %r3, 736(%r4)
	ld %r5, 736(%r6)
	xor %r3, %r3, %r5
	std %r3, 736(%r6)
	ld %r3, 744(%r4)
	ld %r5, 744(%r6)
	xor %r3, %r3, %r5
	std %r3, 744(%r6)
	ld %r3, 752(%r4)
	ld %r5, 752(%r6)
	xor %r3, %r3, %r5
	std %r3, 752(%r6)
	ld %r3, 760(%r4)
	ld %r5, 760(%r6)
	xor %r3, %r3, %r5
	std %r3, 760(%r6)
	ld %r3, 768(%r4)
	ld %r5, 768(%r6)
	xor %r3, %r3, %r5
	std %r3, 768(%r6)
	ld %r3, 776(%r4)
	ld %r5, 776(%r6)
	xor %r3, %r3, %r5
	std %r3, 776(%r6)
	ld %r3, 784(%r4)
	ld %r5, 784(%r6)
	xor %r3, %r3, %r5
	std %r3, 784(%r6)
	ld %r3, 792(%r4)
	ld %r5, 792(%r6)
	xor %r3, %r3, %r5
	std %r3, 792(%r6)
	ld %r3, 800(%r4)
	ld %r5, 800(%r6)
	xor %r3, %r3, %r5
	std %r3, 800(%r6)
	ld %r3, 808(%r4)
	ld %r5, 808(%r6)
	xor %r3, %r3, %r5
	std %r3, 808(%r6)
	ld %r3, 816(%r4)
	ld %r5, 816(%r6)
	xor %r3, %r3, %r5
	std %r3, 816(%r6)
	ld %r3, 824(%r4)
	ld %r5, 824(%r6)
	xor %r3, %r3, %r5
	std %r3, 824(%r6)
	ld %r3, 832(%r4)
	ld %r5, 832(%r6)
	xor %r3, %r3, %r5
	std %r3, 832(%r6)
	ld %r3, 840(%r4)
	ld %r5, 840(%r6)
	xor %r3, %r3, %r5
	std %r3, 840(%r6)
	ld %r3, 848(%r4)
	ld %r5, 848(%r6)
	xor %r3, %r3, %r5
	std %r3, 848(%r6)
	ld %r3, 856(%r4)
	ld %r5, 856(%r6)
	xor %r3, %r3, %r5
	std %r3, 856(%r6)
	ld %r3, 864(%r4)
	ld %r5, 864(%r6)
	xor %r3, %r3, %r5
	std %r3, 864(%r6)
	ld %r3, 872(%r4)
	ld %r5, 872(%r6)
	xor %r3, %r3, %r5
	std %r3, 872(%r6)
	ld %r3, 880(%r4)
	ld %r5, 880(%r6)
	xor %r3, %r3, %r5
	std %r3, 880(%r6)
	ld %r3, 888(%r4)
	ld %r5, 888(%r6)
	xor %r3, %r3, %r5
	std %r3, 888(%r6)
	ld %r3, 896(%r4)
	ld %r5, 896(%r6)
	xor %r3, %r3, %r5
	std %r3, 896(%r6)
	ld %r3, 904(%r4)
	ld %r5, 904(%r6)
	xor %r3, %r3, %r5
	std %r3, 904(%r6)
	ld %r3, 912(%r4)
	ld %r5, 912(%r6)
	xor %r3, %r3, %r5
	std %r3, 912(%r6)
	ld %r3, 920(%r4)
	ld %r5, 920(%r6)
	xor %r3, %r3, %r5
	std %r3, 920(%r6)
	ld %r3, 928(%r4)
	ld %r5, 928(%r6)
	xor %r3, %r3, %r5
	std %r3, 928(%r6)
	ld %r3, 936(%r4)
	ld %r5, 936(%r6)
	xor %r3, %r3, %r5
	std %r3, 936(%r6)
	ld %r3, 944(%r4)
	ld %r5, 944(%r6)
	xor %r3, %r3, %r5
	std %r3, 944(%r6)
	ld %r3, 952(%r4)
	ld %r5, 952(%r6)
	xor %r3, %r3, %r5
	std %r3, 952(%r6)
	ld %r3, 960(%r4)
	ld %r5, 960(%r6)
	xor %r3, %r3, %r5
	std %r3, 960(%r6)
	ld %r3, 968(%r4)
	ld %r5, 968(%r6)
	xor %r3, %r3, %r5
	std %r3, 968(%r6)
	ld %r3, 976(%r4)
	ld %r5, 976(%r6)
	xor %r3, %r3, %r5
	std %r3, 976(%r6)
	ld %r3, 984(%r4)
	ld %r5, 984(%r6)
	xor %r3, %r3, %r5
	std %r3, 984(%r6)
	ld %r3, 992(%r4)
	ld %r5, 992(%r6)
	xor %r3, %r3, %r5
	std %r3, 992(%r6)
	ld %r3, 1000(%r4)
	ld %r5, 1000(%r6)
	xor %r3, %r3, %r5
	std %r3, 1000(%r6)
	ld %r3, 1008(%r4)
	ld %r5, 1008(%r6)
	xor %r3, %r3, %r5
	std %r3, 1008(%r6)
	ld %r3, 1016(%r4)
	ld %r5, 1016(%r6)
	xor %r3, %r3, %r5
	std %r3, 1016(%r6)
	b 227f
226:
	ld %r3, 0(%r4)
	std %r3, 0(%r6)
	ld %r3, 8(%r4)
	std %r3, 8(%r6)
	ld %r3, 16(%r4)
	std %r3, 16(%r6)
	ld %r3, 24(%r4)
	std %r3, 24(%r6)
	ld %r3, 32(%r4)
	std %r3, 32(%r6)
	ld %r3, 40(%r4)
	std %r3, 40(%r6)
	ld %r3, 48(%r4)
	std %r3, 48(%r6)
	ld %r3, 56(%r4)
	std %r3, 56(%r6)
	ld %r3, 64(%r4)
	std %r3, 64(%r6)
	ld %r3, 72(%r4)
	std %r3, 72(%r6)
	ld %r3, 80(%r4)
	std %r3, 80(%r6)
	ld %r3, 88(%r4)
	std %r3, 88(%r6)
	ld %r3, 96(%r4)
	std %r3, 96(%r6)
	ld %r3, 104(%r4)
	std %r3, 104(%r6)
	ld %r3, 112(%r4)
	std %r3, 112(%r6)
	ld %r3, 120(%r4)
	std %r3, 120(%r6)
	ld %r3, 128(%r4)
	std %r3, 128(%r6)
	ld %r3, 136(%r4)
	std %r3, 136(%r6)
	ld %r3, 144(%r4)
	std %r3, 144(%r6)
	ld %r3, 152(%r4)
	std %r3, 152(%r6)
	ld %r3, 160(%r4)
	std %r3, 160(%r6)
	ld %r3, 168(%r4)
	std %r3, 168(%r6)
	ld %r3, 176(%r4)
	std %r3, 176(%r6)
	ld %r3, 184(%r4)
	std %r3, 184(%r6)
	ld %r3, 192(%r4)
	std %r3, 192(%r6)
	ld %r3, 200(%r4)
	std %r3, 200(%r6)
	ld %r3, 208(%r4)
	std %r3, 208(%r6)
	ld %r3, 216(%r4)
	std %r3, 216(%r6)
	ld %r3, 224(%r4)
	std %r3, 224(%r6)
	ld %r3, 232(%r4)
	std %r3, 232(%r6)
	ld %r3, 240(%r4)
	std %r3, 240(%r6)
	ld %r3, 248(%r4)
	std %r3, 248(%r6)
	ld %r3, 256(%r4)
	std %r3, 256(%r6)
	ld %r3, 264(%r4)
	std %r3, 264(%r6)
	ld %r3, 272(%r4)
	std %r3, 272(%r6)
	ld %r3, 280(%r4)
	std %r3, 280(%r6)
	ld %r3, 288(%r4)
	std %r3, 288(%r6)
	ld %r3, 296(%r4)
	std %r3, 296(%r6)
	ld %r3, 304(%r4)
	std %r3, 304(%r6)
	ld %r3, 312(%r4)
	std %r3, 312(%r6)
	ld %r3, 320(%r4)
	std %r3, 320(%r6)
	ld %r3, 328(%r4)
	std %r3, 328(%r6)
	ld %r3, 336(%r4)
	std %r3, 336(%r6)
	ld %r3, 344(%r4)
	std %r3, 344(%r6)
	ld %r3, 352(%r4)
	std %r3, 352(%r6)
	ld %r3, 360(%r4)
	std %r3, 360(%r6)
	ld %r3, 368(%r4)
	std %r3, 368(%r6)
	ld %r3, 376(%r4)
	std %r3, 376(%r6)
	ld %r3, 384(%r4)
	std %r3, 384(%r6)
	ld %r3, 392(%r4)
	std %r3, 392(%r6)
	ld %r3, 400(%r4)
	std %r3, 400(%r6)
	ld %r3, 408(%r4)
	std %r3, 408(%r6)
	ld %r3, 416(%r4)
	std %r3, 416(%r6)
	ld %r3, 424(%r4)
	std %r3, 424(%r6)
	ld %r3, 432(%r4)
	std %r3, 432(%r6)
	ld %r3, 440(%r4)
	std %r3, 440(%r6)
	ld %r3, 448(%r4)
	std %r3, 448(%r6)
	ld %r3, 456(%r4)
	std %r3, 456(%r6)
	ld %r3, 464(%r4)
	std %r3, 464(%r6)
	ld %r3, 472(%r4)
	std %r3, 472(%r6)
	ld %r3, 480(%r4)
	std %r3, 480(%r6)
	ld %r3, 488(%r4)
	std %r3, 488(%r6)
	ld %r3, 496(%r4)
	std %r3, 496(%r6)
	ld %r3, 504(%r4)
	std %r3, 504(%r6)
	ld %r3, 512(%r4)
	std %r3, 512(%r6)
	ld %r3, 520(%r4)
	std %r3, 520(%r6)
	ld %r3, 528(%r4)
	std %r3, 528(%r6)
	ld %r3, 536(%r4)
	std %r3, 536(%r6)
	ld %r3, 544(%r4)
	std %r3, 544(%r6)
	ld %r3, 552(%r4)
	std %r3, 552(%r6)
	ld %r3, 560(%r4)
	std %r3, 560(%r6)
	ld %r3, 568(%r4)
	std %r3, 568(%r6)
	ld %r3, 576(%r4)
	std %r3, 576(%r6)
	ld %r3, 584(%r4)
	std %r3, 584(%r6)
	ld %r3, 592(%r4)
	std %r3, 592(%r6)
	ld %r3, 600(%r4)
	std %r3, 600(%r6)
	ld %r3, 608(%r4)
	std %r3, 608(%r6)
	ld %r3, 616(%r4)
	std %r3, 616(%r6)
	ld %r3, 624(%r4)
	std %r3, 624(%r6)
	ld %r3, 632(%r4)
	std %r3, 632(%r6)
	ld %r3, 640(%r4)
	std %r3, 640(%r6)
	ld %r3, 648(%r4)
	std %r3, 648(%r6)
	ld %r3, 656(%r4)
	std %r3, 656(%r6)
	ld %r3, 664(%r4)
	std %r3, 664(%r6)
	ld %r3, 672(%r4)
	std %r3, 672(%r6)
	ld %r3, 680(%r4)
	std %r3, 680(%r6)
	ld %r3, 688(%r4)
	std %r3, 688(%r6)
	ld %r3, 696(%r4)
	std %r3, 696(%r6)
	ld %r3, 704(%r4)
	std %r3, 704(%r6)
	ld %r3, 712(%r4)
	std %r3, 712(%r6)
	ld %r3, 720(%r4)
	std %r3, 720(%r6)
	ld %r3, 728(%r4)
	std %r3, 728(%r6)
	ld %r3, 736(%r4)
	std %r3, 736(%r6)
	ld %r3, 744(%r4)
	std %r3, 744(%r6)
	ld %r3, 752(%r4)
	std %r3, 752(%r6)
	ld %r3, 760(%r4)
	std %r3, 760(%r6)
	ld %r3, 768(%r4)
	std %r3, 768(%r6)
	ld %r3, 776(%r4)
	std %r3, 776(%r6)
	ld %r3, 784(%r4)
	std %r3, 784(%r6)
	ld %r3, 792(%r4)
	std %r3, 792(%r6)
	ld %r3, 800(%r4)
	std %r3, 800(%r6)
	ld %r3, 808(%r4)
	std %r3, 808(%r6)
	ld %r3, 816(%r4)
	std %r3, 816(%r6)
	ld %r3, 824(%r4)
	std %r3, 824(%r6)
	ld %r3, 832(%r4)
	std %r3, 832(%r6)
	ld %r3, 840(%r4)
	std %r3, 840(%r6)
	ld %r3, 848(%r4)
	std %r3, 848(%r6)
	ld %r3, 856(%r4)
	std %r3, 856(%r6)
	ld %r3, 864(%r4)
	std %r3, 864(%r6)
	ld %r3, 872(%r4)
	std %r3, 872(%r6)
	ld %r3, 880(%r4)
	std %r3, 880(%r6)
	ld %r3, 888(%r4)
	std %r3, 888(%r6)
	ld %r3, 896(%r4)
	std %r3, 896(%r6)
	ld %r3, 904(%r4)
	std %r3, 904(%r6)
	ld %r3, 912(%r4)
	std %r3, 912(%r6)
	ld %r3, 920(%r4)
	std %r3, 920(%r6)
	ld %r3, 928(%r4)
	std %r3, 928(%r6)
	ld %r3, 936(%r4)
	std %r3, 936(%r6)
	ld %r3, 944(%r4)
	std %r3, 944(%r6)
	ld %r3, 952(%r4)
	std %r3, 952(%r6)
	ld %r3, 960(%r4)
	std %r3, 960(%r6)
	ld %r3, 968(%r4)
	std %r3, 968(%r6)
	ld %r3, 976(%r4)
	std %r3, 976(%r6)
	ld %r3, 984(%r4)
	std %r3, 984(%r6)
	ld %r3, 992(%r4)
	std %r3, 992(%r6)
	ld %r3, 1000(%r4)
	std %r3, 1000(%r6)
	ld %r3, 1008(%r4)
	std %r3, 1008(%r6)
	ld %r3, 1016(%r4)
	std %r3, 1016(%r6)
227:
	ld %r3, 232(%r30)
	addi %r3, %r3, 1
	std %r3, 232(%r30)
	ld %r4, 264(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	bne %cr0, 29b
	b 28f
27:
28:
	ld %r3, 216(%r30)
	addi %r3, %r3, 1
	std %r3, 216(%r30)
	lwz %r4, 200(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	bne %cr0, 24b
	ld %r3, 224(%r30)
	addi %r3, %r3, 1
	std %r3, 224(%r30)
	addi %r4, %r3, -4
	cmpldi %cr0, %r4, 0
	bne %cr0, 23b
	ld %r3, 208(%r30)
	addi %r3, %r3, 1
	std %r3, 208(%r30)
	lwz %r4, 184(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	bne %cr0, 22b
	ld %r6, 472(%r30)
	li %r3, 0
	std %r3, 0(%r6)
	std %r3, 8(%r6)
	std %r3, 16(%r6)
	std %r3, 24(%r6)
	std %r3, 32(%r6)
	std %r3, 40(%r6)
	std %r3, 48(%r6)
	std %r3, 56(%r6)
	std %r3, 64(%r6)
	std %r3, 72(%r6)
	std %r3, 80(%r6)
	std %r3, 88(%r6)
	std %r3, 96(%r6)
	std %r3, 104(%r6)
	std %r3, 112(%r6)
	std %r3, 120(%r6)
	std %r3, 128(%r6)
	std %r3, 136(%r6)
	std %r3, 144(%r6)
	std %r3, 152(%r6)
	std %r3, 160(%r6)
	std %r3, 168(%r6)
	std %r3, 176(%r6)
	std %r3, 184(%r6)
	std %r3, 192(%r6)
	std %r3, 200(%r6)
	std %r3, 208(%r6)
	std %r3, 216(%r6)
	std %r3, 224(%r6)
	std %r3, 232(%r6)
	std %r3, 240(%r6)
	std %r3, 248(%r6)
	std %r3, 256(%r6)
	std %r3, 264(%r6)
	std %r3, 272(%r6)
	std %r3, 280(%r6)
	std %r3, 288(%r6)
	std %r3, 296(%r6)
	std %r3, 304(%r6)
	std %r3, 312(%r6)
	std %r3, 320(%r6)
	std %r3, 328(%r6)
	std %r3, 336(%r6)
	std %r3, 344(%r6)
	std %r3, 352(%r6)
	std %r3, 360(%r6)
	std %r3, 368(%r6)
	std %r3, 376(%r6)
	std %r3, 384(%r6)
	std %r3, 392(%r6)
	std %r3, 400(%r6)
	std %r3, 408(%r6)
	std %r3, 416(%r6)
	std %r3, 424(%r6)
	std %r3, 432(%r6)
	std %r3, 440(%r6)
	std %r3, 448(%r6)
	std %r3, 456(%r6)
	std %r3, 464(%r6)
	std %r3, 472(%r6)
	std %r3, 480(%r6)
	std %r3, 488(%r6)
	std %r3, 496(%r6)
	std %r3, 504(%r6)
	std %r3, 512(%r6)
	std %r3, 520(%r6)
	std %r3, 528(%r6)
	std %r3, 536(%r6)
	std %r3, 544(%r6)
	std %r3, 552(%r6)
	std %r3, 560(%r6)
	std %r3, 568(%r6)
	std %r3, 576(%r6)
	std %r3, 584(%r6)
	std %r3, 592(%r6)
	std %r3, 600(%r6)
	std %r3, 608(%r6)
	std %r3, 616(%r6)
	std %r3, 624(%r6)
	std %r3, 632(%r6)
	std %r3, 640(%r6)
	std %r3, 648(%r6)
	std %r3, 656(%r6)
	std %r3, 664(%r6)
	std %r3, 672(%r6)
	std %r3, 680(%r6)
	std %r3, 688(%r6)
	std %r3, 696(%r6)
	std %r3, 704(%r6)
	std %r3, 712(%r6)
	std %r3, 720(%r6)
	std %r3, 728(%r6)
	std %r3, 736(%r6)
	std %r3, 744(%r6)
	std %r3, 752(%r6)
	std %r3, 760(%r6)
	std %r3, 768(%r6)
	std %r3, 776(%r6)
	std %r3, 784(%r6)
	std %r3, 792(%r6)
	std %r3, 800(%r6)
	std %r3, 808(%r6)
	std %r3, 816(%r6)
	std %r3, 824(%r6)
	std %r3, 832(%r6)
	std %r3, 840(%r6)
	std %r3, 848(%r6)
	std %r3, 856(%r6)
	std %r3, 864(%r6)
	std %r3, 872(%r6)
	std %r3, 880(%r6)
	std %r3, 888(%r6)
	std %r3, 896(%r6)
	std %r3, 904(%r6)
	std %r3, 912(%r6)
	std %r3, 920(%r6)
	std %r3, 928(%r6)
	std %r3, 936(%r6)
	std %r3, 944(%r6)
	std %r3, 952(%r6)
	std %r3, 960(%r6)
	std %r3, 968(%r6)
	std %r3, 976(%r6)
	std %r3, 984(%r6)
	std %r3, 992(%r6)
	std %r3, 1000(%r6)
	std %r3, 1008(%r6)
	std %r3, 1016(%r6)
	li %r3, 0
	std %r3, 216(%r30)
228:
	ld %r3, 216(%r30)
	ld %r4, 248(%r30)
	addi %r4, %r4, -1
	ld %r5, 248(%r30)
	mulld %r3, %r3, %r5
	add %r3, %r3, %r4
	rldicr %r3, %r3, 10, 53
	ld %r5, 472(%r30)
	add %r3, %r5, %r3
	addi %r4, %r3, 0
	ld %r6, 472(%r30)
	ld %r3, 0(%r4)
	ld %r5, 0(%r6)
	xor %r3, %r3, %r5
	std %r3, 0(%r6)
	ld %r3, 8(%r4)
	ld %r5, 8(%r6)
	xor %r3, %r3, %r5
	std %r3, 8(%r6)
	ld %r3, 16(%r4)
	ld %r5, 16(%r6)
	xor %r3, %r3, %r5
	std %r3, 16(%r6)
	ld %r3, 24(%r4)
	ld %r5, 24(%r6)
	xor %r3, %r3, %r5
	std %r3, 24(%r6)
	ld %r3, 32(%r4)
	ld %r5, 32(%r6)
	xor %r3, %r3, %r5
	std %r3, 32(%r6)
	ld %r3, 40(%r4)
	ld %r5, 40(%r6)
	xor %r3, %r3, %r5
	std %r3, 40(%r6)
	ld %r3, 48(%r4)
	ld %r5, 48(%r6)
	xor %r3, %r3, %r5
	std %r3, 48(%r6)
	ld %r3, 56(%r4)
	ld %r5, 56(%r6)
	xor %r3, %r3, %r5
	std %r3, 56(%r6)
	ld %r3, 64(%r4)
	ld %r5, 64(%r6)
	xor %r3, %r3, %r5
	std %r3, 64(%r6)
	ld %r3, 72(%r4)
	ld %r5, 72(%r6)
	xor %r3, %r3, %r5
	std %r3, 72(%r6)
	ld %r3, 80(%r4)
	ld %r5, 80(%r6)
	xor %r3, %r3, %r5
	std %r3, 80(%r6)
	ld %r3, 88(%r4)
	ld %r5, 88(%r6)
	xor %r3, %r3, %r5
	std %r3, 88(%r6)
	ld %r3, 96(%r4)
	ld %r5, 96(%r6)
	xor %r3, %r3, %r5
	std %r3, 96(%r6)
	ld %r3, 104(%r4)
	ld %r5, 104(%r6)
	xor %r3, %r3, %r5
	std %r3, 104(%r6)
	ld %r3, 112(%r4)
	ld %r5, 112(%r6)
	xor %r3, %r3, %r5
	std %r3, 112(%r6)
	ld %r3, 120(%r4)
	ld %r5, 120(%r6)
	xor %r3, %r3, %r5
	std %r3, 120(%r6)
	ld %r3, 128(%r4)
	ld %r5, 128(%r6)
	xor %r3, %r3, %r5
	std %r3, 128(%r6)
	ld %r3, 136(%r4)
	ld %r5, 136(%r6)
	xor %r3, %r3, %r5
	std %r3, 136(%r6)
	ld %r3, 144(%r4)
	ld %r5, 144(%r6)
	xor %r3, %r3, %r5
	std %r3, 144(%r6)
	ld %r3, 152(%r4)
	ld %r5, 152(%r6)
	xor %r3, %r3, %r5
	std %r3, 152(%r6)
	ld %r3, 160(%r4)
	ld %r5, 160(%r6)
	xor %r3, %r3, %r5
	std %r3, 160(%r6)
	ld %r3, 168(%r4)
	ld %r5, 168(%r6)
	xor %r3, %r3, %r5
	std %r3, 168(%r6)
	ld %r3, 176(%r4)
	ld %r5, 176(%r6)
	xor %r3, %r3, %r5
	std %r3, 176(%r6)
	ld %r3, 184(%r4)
	ld %r5, 184(%r6)
	xor %r3, %r3, %r5
	std %r3, 184(%r6)
	ld %r3, 192(%r4)
	ld %r5, 192(%r6)
	xor %r3, %r3, %r5
	std %r3, 192(%r6)
	ld %r3, 200(%r4)
	ld %r5, 200(%r6)
	xor %r3, %r3, %r5
	std %r3, 200(%r6)
	ld %r3, 208(%r4)
	ld %r5, 208(%r6)
	xor %r3, %r3, %r5
	std %r3, 208(%r6)
	ld %r3, 216(%r4)
	ld %r5, 216(%r6)
	xor %r3, %r3, %r5
	std %r3, 216(%r6)
	ld %r3, 224(%r4)
	ld %r5, 224(%r6)
	xor %r3, %r3, %r5
	std %r3, 224(%r6)
	ld %r3, 232(%r4)
	ld %r5, 232(%r6)
	xor %r3, %r3, %r5
	std %r3, 232(%r6)
	ld %r3, 240(%r4)
	ld %r5, 240(%r6)
	xor %r3, %r3, %r5
	std %r3, 240(%r6)
	ld %r3, 248(%r4)
	ld %r5, 248(%r6)
	xor %r3, %r3, %r5
	std %r3, 248(%r6)
	ld %r3, 256(%r4)
	ld %r5, 256(%r6)
	xor %r3, %r3, %r5
	std %r3, 256(%r6)
	ld %r3, 264(%r4)
	ld %r5, 264(%r6)
	xor %r3, %r3, %r5
	std %r3, 264(%r6)
	ld %r3, 272(%r4)
	ld %r5, 272(%r6)
	xor %r3, %r3, %r5
	std %r3, 272(%r6)
	ld %r3, 280(%r4)
	ld %r5, 280(%r6)
	xor %r3, %r3, %r5
	std %r3, 280(%r6)
	ld %r3, 288(%r4)
	ld %r5, 288(%r6)
	xor %r3, %r3, %r5
	std %r3, 288(%r6)
	ld %r3, 296(%r4)
	ld %r5, 296(%r6)
	xor %r3, %r3, %r5
	std %r3, 296(%r6)
	ld %r3, 304(%r4)
	ld %r5, 304(%r6)
	xor %r3, %r3, %r5
	std %r3, 304(%r6)
	ld %r3, 312(%r4)
	ld %r5, 312(%r6)
	xor %r3, %r3, %r5
	std %r3, 312(%r6)
	ld %r3, 320(%r4)
	ld %r5, 320(%r6)
	xor %r3, %r3, %r5
	std %r3, 320(%r6)
	ld %r3, 328(%r4)
	ld %r5, 328(%r6)
	xor %r3, %r3, %r5
	std %r3, 328(%r6)
	ld %r3, 336(%r4)
	ld %r5, 336(%r6)
	xor %r3, %r3, %r5
	std %r3, 336(%r6)
	ld %r3, 344(%r4)
	ld %r5, 344(%r6)
	xor %r3, %r3, %r5
	std %r3, 344(%r6)
	ld %r3, 352(%r4)
	ld %r5, 352(%r6)
	xor %r3, %r3, %r5
	std %r3, 352(%r6)
	ld %r3, 360(%r4)
	ld %r5, 360(%r6)
	xor %r3, %r3, %r5
	std %r3, 360(%r6)
	ld %r3, 368(%r4)
	ld %r5, 368(%r6)
	xor %r3, %r3, %r5
	std %r3, 368(%r6)
	ld %r3, 376(%r4)
	ld %r5, 376(%r6)
	xor %r3, %r3, %r5
	std %r3, 376(%r6)
	ld %r3, 384(%r4)
	ld %r5, 384(%r6)
	xor %r3, %r3, %r5
	std %r3, 384(%r6)
	ld %r3, 392(%r4)
	ld %r5, 392(%r6)
	xor %r3, %r3, %r5
	std %r3, 392(%r6)
	ld %r3, 400(%r4)
	ld %r5, 400(%r6)
	xor %r3, %r3, %r5
	std %r3, 400(%r6)
	ld %r3, 408(%r4)
	ld %r5, 408(%r6)
	xor %r3, %r3, %r5
	std %r3, 408(%r6)
	ld %r3, 416(%r4)
	ld %r5, 416(%r6)
	xor %r3, %r3, %r5
	std %r3, 416(%r6)
	ld %r3, 424(%r4)
	ld %r5, 424(%r6)
	xor %r3, %r3, %r5
	std %r3, 424(%r6)
	ld %r3, 432(%r4)
	ld %r5, 432(%r6)
	xor %r3, %r3, %r5
	std %r3, 432(%r6)
	ld %r3, 440(%r4)
	ld %r5, 440(%r6)
	xor %r3, %r3, %r5
	std %r3, 440(%r6)
	ld %r3, 448(%r4)
	ld %r5, 448(%r6)
	xor %r3, %r3, %r5
	std %r3, 448(%r6)
	ld %r3, 456(%r4)
	ld %r5, 456(%r6)
	xor %r3, %r3, %r5
	std %r3, 456(%r6)
	ld %r3, 464(%r4)
	ld %r5, 464(%r6)
	xor %r3, %r3, %r5
	std %r3, 464(%r6)
	ld %r3, 472(%r4)
	ld %r5, 472(%r6)
	xor %r3, %r3, %r5
	std %r3, 472(%r6)
	ld %r3, 480(%r4)
	ld %r5, 480(%r6)
	xor %r3, %r3, %r5
	std %r3, 480(%r6)
	ld %r3, 488(%r4)
	ld %r5, 488(%r6)
	xor %r3, %r3, %r5
	std %r3, 488(%r6)
	ld %r3, 496(%r4)
	ld %r5, 496(%r6)
	xor %r3, %r3, %r5
	std %r3, 496(%r6)
	ld %r3, 504(%r4)
	ld %r5, 504(%r6)
	xor %r3, %r3, %r5
	std %r3, 504(%r6)
	ld %r3, 512(%r4)
	ld %r5, 512(%r6)
	xor %r3, %r3, %r5
	std %r3, 512(%r6)
	ld %r3, 520(%r4)
	ld %r5, 520(%r6)
	xor %r3, %r3, %r5
	std %r3, 520(%r6)
	ld %r3, 528(%r4)
	ld %r5, 528(%r6)
	xor %r3, %r3, %r5
	std %r3, 528(%r6)
	ld %r3, 536(%r4)
	ld %r5, 536(%r6)
	xor %r3, %r3, %r5
	std %r3, 536(%r6)
	ld %r3, 544(%r4)
	ld %r5, 544(%r6)
	xor %r3, %r3, %r5
	std %r3, 544(%r6)
	ld %r3, 552(%r4)
	ld %r5, 552(%r6)
	xor %r3, %r3, %r5
	std %r3, 552(%r6)
	ld %r3, 560(%r4)
	ld %r5, 560(%r6)
	xor %r3, %r3, %r5
	std %r3, 560(%r6)
	ld %r3, 568(%r4)
	ld %r5, 568(%r6)
	xor %r3, %r3, %r5
	std %r3, 568(%r6)
	ld %r3, 576(%r4)
	ld %r5, 576(%r6)
	xor %r3, %r3, %r5
	std %r3, 576(%r6)
	ld %r3, 584(%r4)
	ld %r5, 584(%r6)
	xor %r3, %r3, %r5
	std %r3, 584(%r6)
	ld %r3, 592(%r4)
	ld %r5, 592(%r6)
	xor %r3, %r3, %r5
	std %r3, 592(%r6)
	ld %r3, 600(%r4)
	ld %r5, 600(%r6)
	xor %r3, %r3, %r5
	std %r3, 600(%r6)
	ld %r3, 608(%r4)
	ld %r5, 608(%r6)
	xor %r3, %r3, %r5
	std %r3, 608(%r6)
	ld %r3, 616(%r4)
	ld %r5, 616(%r6)
	xor %r3, %r3, %r5
	std %r3, 616(%r6)
	ld %r3, 624(%r4)
	ld %r5, 624(%r6)
	xor %r3, %r3, %r5
	std %r3, 624(%r6)
	ld %r3, 632(%r4)
	ld %r5, 632(%r6)
	xor %r3, %r3, %r5
	std %r3, 632(%r6)
	ld %r3, 640(%r4)
	ld %r5, 640(%r6)
	xor %r3, %r3, %r5
	std %r3, 640(%r6)
	ld %r3, 648(%r4)
	ld %r5, 648(%r6)
	xor %r3, %r3, %r5
	std %r3, 648(%r6)
	ld %r3, 656(%r4)
	ld %r5, 656(%r6)
	xor %r3, %r3, %r5
	std %r3, 656(%r6)
	ld %r3, 664(%r4)
	ld %r5, 664(%r6)
	xor %r3, %r3, %r5
	std %r3, 664(%r6)
	ld %r3, 672(%r4)
	ld %r5, 672(%r6)
	xor %r3, %r3, %r5
	std %r3, 672(%r6)
	ld %r3, 680(%r4)
	ld %r5, 680(%r6)
	xor %r3, %r3, %r5
	std %r3, 680(%r6)
	ld %r3, 688(%r4)
	ld %r5, 688(%r6)
	xor %r3, %r3, %r5
	std %r3, 688(%r6)
	ld %r3, 696(%r4)
	ld %r5, 696(%r6)
	xor %r3, %r3, %r5
	std %r3, 696(%r6)
	ld %r3, 704(%r4)
	ld %r5, 704(%r6)
	xor %r3, %r3, %r5
	std %r3, 704(%r6)
	ld %r3, 712(%r4)
	ld %r5, 712(%r6)
	xor %r3, %r3, %r5
	std %r3, 712(%r6)
	ld %r3, 720(%r4)
	ld %r5, 720(%r6)
	xor %r3, %r3, %r5
	std %r3, 720(%r6)
	ld %r3, 728(%r4)
	ld %r5, 728(%r6)
	xor %r3, %r3, %r5
	std %r3, 728(%r6)
	ld %r3, 736(%r4)
	ld %r5, 736(%r6)
	xor %r3, %r3, %r5
	std %r3, 736(%r6)
	ld %r3, 744(%r4)
	ld %r5, 744(%r6)
	xor %r3, %r3, %r5
	std %r3, 744(%r6)
	ld %r3, 752(%r4)
	ld %r5, 752(%r6)
	xor %r3, %r3, %r5
	std %r3, 752(%r6)
	ld %r3, 760(%r4)
	ld %r5, 760(%r6)
	xor %r3, %r3, %r5
	std %r3, 760(%r6)
	ld %r3, 768(%r4)
	ld %r5, 768(%r6)
	xor %r3, %r3, %r5
	std %r3, 768(%r6)
	ld %r3, 776(%r4)
	ld %r5, 776(%r6)
	xor %r3, %r3, %r5
	std %r3, 776(%r6)
	ld %r3, 784(%r4)
	ld %r5, 784(%r6)
	xor %r3, %r3, %r5
	std %r3, 784(%r6)
	ld %r3, 792(%r4)
	ld %r5, 792(%r6)
	xor %r3, %r3, %r5
	std %r3, 792(%r6)
	ld %r3, 800(%r4)
	ld %r5, 800(%r6)
	xor %r3, %r3, %r5
	std %r3, 800(%r6)
	ld %r3, 808(%r4)
	ld %r5, 808(%r6)
	xor %r3, %r3, %r5
	std %r3, 808(%r6)
	ld %r3, 816(%r4)
	ld %r5, 816(%r6)
	xor %r3, %r3, %r5
	std %r3, 816(%r6)
	ld %r3, 824(%r4)
	ld %r5, 824(%r6)
	xor %r3, %r3, %r5
	std %r3, 824(%r6)
	ld %r3, 832(%r4)
	ld %r5, 832(%r6)
	xor %r3, %r3, %r5
	std %r3, 832(%r6)
	ld %r3, 840(%r4)
	ld %r5, 840(%r6)
	xor %r3, %r3, %r5
	std %r3, 840(%r6)
	ld %r3, 848(%r4)
	ld %r5, 848(%r6)
	xor %r3, %r3, %r5
	std %r3, 848(%r6)
	ld %r3, 856(%r4)
	ld %r5, 856(%r6)
	xor %r3, %r3, %r5
	std %r3, 856(%r6)
	ld %r3, 864(%r4)
	ld %r5, 864(%r6)
	xor %r3, %r3, %r5
	std %r3, 864(%r6)
	ld %r3, 872(%r4)
	ld %r5, 872(%r6)
	xor %r3, %r3, %r5
	std %r3, 872(%r6)
	ld %r3, 880(%r4)
	ld %r5, 880(%r6)
	xor %r3, %r3, %r5
	std %r3, 880(%r6)
	ld %r3, 888(%r4)
	ld %r5, 888(%r6)
	xor %r3, %r3, %r5
	std %r3, 888(%r6)
	ld %r3, 896(%r4)
	ld %r5, 896(%r6)
	xor %r3, %r3, %r5
	std %r3, 896(%r6)
	ld %r3, 904(%r4)
	ld %r5, 904(%r6)
	xor %r3, %r3, %r5
	std %r3, 904(%r6)
	ld %r3, 912(%r4)
	ld %r5, 912(%r6)
	xor %r3, %r3, %r5
	std %r3, 912(%r6)
	ld %r3, 920(%r4)
	ld %r5, 920(%r6)
	xor %r3, %r3, %r5
	std %r3, 920(%r6)
	ld %r3, 928(%r4)
	ld %r5, 928(%r6)
	xor %r3, %r3, %r5
	std %r3, 928(%r6)
	ld %r3, 936(%r4)
	ld %r5, 936(%r6)
	xor %r3, %r3, %r5
	std %r3, 936(%r6)
	ld %r3, 944(%r4)
	ld %r5, 944(%r6)
	xor %r3, %r3, %r5
	std %r3, 944(%r6)
	ld %r3, 952(%r4)
	ld %r5, 952(%r6)
	xor %r3, %r3, %r5
	std %r3, 952(%r6)
	ld %r3, 960(%r4)
	ld %r5, 960(%r6)
	xor %r3, %r3, %r5
	std %r3, 960(%r6)
	ld %r3, 968(%r4)
	ld %r5, 968(%r6)
	xor %r3, %r3, %r5
	std %r3, 968(%r6)
	ld %r3, 976(%r4)
	ld %r5, 976(%r6)
	xor %r3, %r3, %r5
	std %r3, 976(%r6)
	ld %r3, 984(%r4)
	ld %r5, 984(%r6)
	xor %r3, %r3, %r5
	std %r3, 984(%r6)
	ld %r3, 992(%r4)
	ld %r5, 992(%r6)
	xor %r3, %r3, %r5
	std %r3, 992(%r6)
	ld %r3, 1000(%r4)
	ld %r5, 1000(%r6)
	xor %r3, %r3, %r5
	std %r3, 1000(%r6)
	ld %r3, 1008(%r4)
	ld %r5, 1008(%r6)
	xor %r3, %r3, %r5
	std %r3, 1008(%r6)
	ld %r3, 1016(%r4)
	ld %r5, 1016(%r6)
	xor %r3, %r3, %r5
	std %r3, 1016(%r6)
	ld %r3, 216(%r30)
	addi %r3, %r3, 1
	std %r3, 216(%r30)
	lwz %r4, 200(%r30)
	subf %r4, %r4, %r3
	cmpldi %cr0, %r4, 0
	bne %cr0, 228b
	ld %r3, 472(%r30)
	li %r4, 1024
	ld %r5, 496(%r30)
	ld %r6, 504(%r30)
	addi %r7, %r31, 0
	bl {vg_argon2_hprime}
	ld %r0, 104(%r30)
	mtlr %r0
	ld %r28, 112(%r30)
	ld %r29, 120(%r30)
	ld %r31, 136(%r30)
	ld %r30, 128(%r30)
	addi %r1, %r1, 336
	blr
