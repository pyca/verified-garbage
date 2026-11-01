// The functions of `src/internal/vg_argon2_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
