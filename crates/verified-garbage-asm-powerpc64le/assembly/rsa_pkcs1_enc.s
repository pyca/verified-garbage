// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_precomputed:
	stdu %r1, -320(%r1)
	addi %r12, %r1, 0
	mflr %r0
	std %r0, 312(%r12)
	std %r3, 208(%r12)
	std %r5, 216(%r12)
	std %r6, 224(%r12)
	std %r7, 232(%r12)
	std %r8, 240(%r12)
	std %r9, 248(%r12)
	std %r10, 256(%r12)
	ld %r0, 416(%r12)
	std %r0, 264(%r12)
	ld %r0, 424(%r12)
	std %r0, 272(%r12)
	ld %r0, 520(%r12)
	std %r0, 280(%r12)
	ld %r0, 440(%r12)
	std %r0, 96(%r12)
	ld %r0, 448(%r12)
	std %r0, 104(%r12)
	ld %r0, 456(%r12)
	std %r0, 112(%r12)
	ld %r0, 464(%r12)
	std %r0, 120(%r12)
	ld %r0, 472(%r12)
	std %r0, 128(%r12)
	ld %r0, 480(%r12)
	std %r0, 136(%r12)
	ld %r0, 488(%r12)
	std %r0, 144(%r12)
	ld %r0, 496(%r12)
	std %r0, 152(%r12)
	ld %r0, 504(%r12)
	std %r0, 160(%r12)
	ld %r0, 512(%r12)
	std %r0, 168(%r12)
	ld %r0, 520(%r12)
	std %r0, 176(%r12)
	ld %r0, 528(%r12)
	std %r0, 184(%r12)
	ld %r0, 536(%r12)
	std %r0, 192(%r12)
	ld %r0, 544(%r12)
	std %r0, 200(%r12)
	or %r4, %r7, %r7
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	ld %r9, 272(%r12)
	or %r10, %r4, %r4
	bl {vg_rsa_private_checked_precomputed}
	rlwinm %r3, %r3, 0, 0, 31
	addi %r12, %r1, 0
	std %r3, 288(%r12)
	ld %r11, 280(%r12)
	addi %r11, %r11, 2416
	ld %r9, 232(%r12)
	li %r0, 0
20:
	stb %r0, 0(%r11)
	addi %r11, %r11, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	ld %r10, 256(%r12)
	ld %r9, 264(%r12)
	ld %r11, 280(%r12)
	addi %r11, %r11, 2416
	ld %r8, 232(%r12)
	add %r11, %r11, %r8
	subf %r11, %r9, %r11
21:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 21b
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	bl {vg_sha256_init}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	li %r4, 0
	ld %r5, 280(%r12)
	addi %r5, %r5, 2416
	ld %r6, 232(%r12)
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 232(%r12)
	ld %r5, 280(%r12)
	addi %r5, %r5, 1040
	ld %r6, 280(%r12)
	addi %r6, %r6, 192
	bl {vg_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	ld %r5, 280(%r12)
	addi %r5, %r5, 1040
	li %r6, 32
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 272(%r12)
	ld %r6, 232(%r12)
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	ld %r5, 232(%r12)
	addi %r5, %r5, 64
	ld %r6, 280(%r12)
	addi %r6, %r6, 1104
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	li %r10, 0
	std %r10, 296(%r12)
	ld %r10, 232(%r12)
	addi %r10, %r10, 31
	rldicl %r10, %r10, 59, 5
	std %r10, 304(%r12)
22:
	addi %r12, %r1, 0
	ld %r9, 280(%r12)
	addi %r9, %r9, 1024
	ld %r11, 296(%r12)
	ld %r8, 232(%r12)
	li %r10, 0
	stb %r10, 0(%r9)
	stb %r11, 1(%r9)
	li %r10, 108
	stb %r10, 2(%r9)
	li %r10, 101
	stb %r10, 3(%r9)
	li %r10, 110
	stb %r10, 4(%r9)
	li %r10, 103
	stb %r10, 5(%r9)
	li %r10, 116
	stb %r10, 6(%r9)
	li %r10, 104
	stb %r10, 7(%r9)
	li %r10, 8
	stb %r10, 8(%r9)
	li %r10, 0
	stb %r10, 9(%r9)
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	ld %r5, 280(%r12)
	addi %r5, %r5, 1104
	li %r6, 32
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 280(%r12)
	addi %r5, %r5, 1024
	li %r6, 10
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	li %r5, 74
	ld %r6, 296(%r12)
	rldicr %r6, %r6, 5, 58
	ld %r10, 280(%r12)
	addi %r10, %r10, 1136
	add %r6, %r6, %r10
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r11, 296(%r12)
	addi %r11, %r11, 1
	std %r11, 296(%r12)
	li %r9, 8
	subf %r9, %r11, %r9
	cmpldi %cr0, %r9, 0
	bne %cr0, 22b
	addi %r12, %r1, 0
	li %r10, 0
	std %r10, 296(%r12)
23:
	addi %r12, %r1, 0
	ld %r9, 280(%r12)
	addi %r9, %r9, 1024
	ld %r11, 296(%r12)
	ld %r8, 232(%r12)
	li %r10, 0
	stb %r10, 0(%r9)
	stb %r11, 1(%r9)
	li %r10, 109
	stb %r10, 2(%r9)
	li %r10, 101
	stb %r10, 3(%r9)
	li %r10, 115
	stb %r10, 4(%r9)
	li %r10, 115
	stb %r10, 5(%r9)
	li %r10, 97
	stb %r10, 6(%r9)
	li %r10, 103
	stb %r10, 7(%r9)
	li %r10, 101
	stb %r10, 8(%r9)
	rldicr %r10, %r8, 3, 60
	stb %r10, 10(%r9)
	rldicl %r10, %r10, 56, 8
	stb %r10, 9(%r9)
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	ld %r5, 280(%r12)
	addi %r5, %r5, 1104
	li %r6, 32
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_init_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	li %r4, 64
	ld %r5, 280(%r12)
	addi %r5, %r5, 1024
	li %r6, 11
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_sha256_update_scratch}
	addi %r12, %r1, 0
	ld %r3, 280(%r12)
	addi %r3, %r3, 0
	ld %r4, 280(%r12)
	addi %r4, %r4, 96
	li %r5, 75
	ld %r6, 296(%r12)
	rldicr %r6, %r6, 5, 58
	ld %r10, 280(%r12)
	addi %r10, %r10, 1392
	add %r6, %r6, %r10
	ld %r7, 280(%r12)
	addi %r7, %r7, 192
	bl {vg_hmac_sha256_finalize_scratch}
	addi %r12, %r1, 0
	ld %r11, 296(%r12)
	addi %r11, %r11, 1
	std %r11, 296(%r12)
	ld %r9, 304(%r12)
	subf %r9, %r11, %r9
	cmpldi %cr0, %r9, 0
	bne %cr0, 23b
	addi %r12, %r1, 0
	ld %r9, 232(%r12)
	addi %r9, %r9, -11
	li %r8, 0
24:
	add %r8, %r8, %r8
	addi %r8, %r8, 1
	subf %r10, %r9, %r8
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	addi %r12, %r1, 0
	ld %r11, 280(%r12)
	addi %r11, %r11, 1136
	li %r7, 128
	li %r6, 0
25:
	lbz %r10, 0(%r11)
	rldicr %r10, %r10, 8, 55
	lbz %r5, 1(%r11)
	add %r10, %r10, %r5
	and %r10, %r10, %r8
	subf %r5, %r10, %r9
	rldicl %r5, %r5, 1, 63
	addi %r5, %r5, -1
	xor %r4, %r6, %r10
	and %r4, %r4, %r5
	xor %r6, %r6, %r4
	addi %r11, %r11, 2
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 25b
	addi %r12, %r1, 0
	ld %r11, 208(%r12)
	addi %r11, %r11, 2
	ld %r7, 232(%r12)
	addi %r7, %r7, -2
	li %r4, 2
	li %r5, 0
	li %r3, 0
	li %r0, 0
	li %r8, 0
	addi %r8, %r8, -1
26:
	lbz %r10, 0(%r11)
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	subf %r10, %r10, %r0
	xor %r9, %r5, %r8
	and %r9, %r9, %r10
	and %r9, %r9, %r4
	or %r3, %r3, %r9
	or %r5, %r5, %r10
	addi %r4, %r4, 1
	addi %r11, %r11, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 26b
	addi %r12, %r1, 0
	ld %r11, 208(%r12)
	ld %r7, 232(%r12)
	lbz %r10, 0(%r11)
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	subf %r10, %r10, %r0
	lbz %r9, 1(%r11)
	li %r4, 2
	xor %r9, %r9, %r4
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	subf %r9, %r9, %r0
	and %r10, %r10, %r9
	and %r5, %r5, %r10
	li %r4, 10
	subf %r9, %r4, %r3
	rldicl %r9, %r9, 1, 63
	subf %r9, %r9, %r0
	xor %r9, %r9, %r8
	and %r5, %r5, %r9
	subf %r9, %r3, %r7
	addi %r9, %r9, -1
	xor %r9, %r9, %r6
	and %r9, %r9, %r5
	xor %r6, %r6, %r9
	ld %r4, 288(%r12)
	li %r9, 1
	xor %r4, %r4, %r9
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	subf %r4, %r4, %r0
	subf %r3, %r6, %r7
	and %r6, %r6, %r4
	ld %r10, 216(%r12)
	std %r6, 0(%r10)
	ld %r10, 280(%r12)
	addi %r10, %r10, 1392
	li %r9, 0
27:
	lbz %r6, 0(%r11)
	lbz %r12, 0(%r10)
	xor %r6, %r6, %r12
	and %r6, %r6, %r5
	xor %r6, %r6, %r12
	subf %r12, %r3, %r9
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r0
	xor %r12, %r12, %r8
	and %r12, %r12, %r4
	and %r6, %r6, %r12
	stb %r6, 0(%r11)
	addi %r9, %r9, 1
	addi %r11, %r11, 1
	addi %r10, %r10, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 27b
	addi %r12, %r1, 0
	ld %r3, 288(%r12)
	ld %r0, 312(%r12)
	mtlr %r0
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3648(%r1)
	addi %r12, %r1, 32
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
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	std %r0, 2192(%r12)
	std %r0, 2200(%r12)
	std %r0, 2208(%r12)
	std %r0, 2216(%r12)
	std %r0, 2224(%r12)
	std %r0, 2232(%r12)
	std %r0, 2240(%r12)
	std %r0, 2248(%r12)
	std %r0, 2256(%r12)
	std %r0, 2264(%r12)
	std %r0, 2272(%r12)
	std %r0, 2280(%r12)
	std %r0, 2288(%r12)
	std %r0, 2296(%r12)
	std %r0, 2304(%r12)
	std %r0, 2312(%r12)
	std %r0, 2320(%r12)
	std %r0, 2328(%r12)
	std %r0, 2336(%r12)
	std %r0, 2344(%r12)
	std %r0, 2352(%r12)
	std %r0, 2360(%r12)
	std %r0, 2368(%r12)
	std %r0, 2376(%r12)
	std %r0, 2384(%r12)
	std %r0, 2392(%r12)
	std %r0, 2400(%r12)
	std %r0, 2408(%r12)
	std %r0, 2416(%r12)
	std %r0, 2424(%r12)
	std %r0, 2432(%r12)
	std %r0, 2440(%r12)
	std %r0, 2448(%r12)
	std %r0, 2456(%r12)
	std %r0, 2464(%r12)
	std %r0, 2472(%r12)
	std %r0, 2480(%r12)
	std %r0, 2488(%r12)
	std %r0, 2496(%r12)
	std %r0, 2504(%r12)
	std %r0, 2512(%r12)
	std %r0, 2520(%r12)
	std %r0, 2528(%r12)
	std %r0, 2536(%r12)
	std %r0, 2544(%r12)
	std %r0, 2552(%r12)
	std %r0, 2560(%r12)
	std %r0, 2568(%r12)
	std %r0, 2576(%r12)
	std %r0, 2584(%r12)
	std %r0, 2592(%r12)
	std %r0, 2600(%r12)
	std %r0, 2608(%r12)
	std %r0, 2616(%r12)
	std %r0, 2624(%r12)
	std %r0, 2632(%r12)
	std %r0, 2640(%r12)
	std %r0, 2648(%r12)
	std %r0, 2656(%r12)
	std %r0, 2664(%r12)
	std %r0, 2672(%r12)
	std %r0, 2680(%r12)
	std %r0, 2688(%r12)
	std %r0, 2696(%r12)
	std %r0, 2704(%r12)
	std %r0, 2712(%r12)
	std %r0, 2720(%r12)
	std %r0, 2728(%r12)
	std %r0, 2736(%r12)
	std %r0, 2744(%r12)
	std %r0, 2752(%r12)
	std %r0, 2760(%r12)
	std %r0, 2768(%r12)
	std %r0, 2776(%r12)
	std %r0, 2784(%r12)
	std %r0, 2792(%r12)
	std %r0, 2800(%r12)
	std %r0, 2808(%r12)
	std %r0, 2816(%r12)
	std %r0, 2824(%r12)
	std %r0, 2832(%r12)
	std %r0, 2840(%r12)
	std %r0, 2848(%r12)
	std %r0, 2856(%r12)
	std %r0, 2864(%r12)
	std %r0, 2872(%r12)
	std %r0, 2880(%r12)
	std %r0, 2888(%r12)
	std %r0, 2896(%r12)
	std %r0, 2904(%r12)
	std %r0, 2912(%r12)
	std %r0, 2920(%r12)
	std %r0, 2928(%r12)
	std %r0, 2936(%r12)
	std %r0, 2944(%r12)
	std %r0, 2952(%r12)
	std %r0, 2960(%r12)
	std %r0, 2968(%r12)
	std %r0, 2976(%r12)
	std %r0, 2984(%r12)
	std %r0, 2992(%r12)
	std %r0, 3000(%r12)
	std %r0, 3008(%r12)
	std %r0, 3016(%r12)
	std %r0, 3024(%r12)
	std %r0, 3032(%r12)
	std %r0, 3040(%r12)
	std %r0, 3048(%r12)
	std %r0, 3056(%r12)
	std %r0, 3064(%r12)
	std %r0, 3072(%r12)
	std %r0, 3080(%r12)
	std %r0, 3088(%r12)
	std %r0, 3096(%r12)
	std %r0, 3104(%r12)
	std %r0, 3112(%r12)
	std %r0, 3120(%r12)
	std %r0, 3128(%r12)
	std %r0, 3136(%r12)
	std %r0, 3144(%r12)
	std %r0, 3152(%r12)
	std %r0, 3160(%r12)
	std %r0, 3168(%r12)
	std %r0, 3176(%r12)
	std %r0, 3184(%r12)
	std %r0, 3192(%r12)
	std %r0, 3200(%r12)
	std %r0, 3208(%r12)
	std %r0, 3216(%r12)
	std %r0, 3224(%r12)
	std %r0, 3232(%r12)
	std %r0, 3240(%r12)
	std %r0, 3248(%r12)
	std %r0, 3256(%r12)
	std %r0, 3264(%r12)
	std %r0, 3272(%r12)
	std %r0, 3280(%r12)
	std %r0, 3288(%r12)
	std %r0, 3296(%r12)
	std %r0, 3304(%r12)
	std %r0, 3312(%r12)
	std %r0, 3320(%r12)
	std %r0, 3328(%r12)
	std %r0, 3336(%r12)
	std %r0, 3344(%r12)
	std %r0, 3352(%r12)
	std %r0, 3360(%r12)
	std %r0, 3368(%r12)
	std %r0, 3376(%r12)
	std %r0, 3384(%r12)
	std %r0, 3392(%r12)
	std %r0, 3400(%r12)
	std %r0, 3408(%r12)
	std %r0, 3416(%r12)
	std %r0, 3424(%r12)
	std %r0, 3432(%r12)
	std %r0, 3440(%r12)
	std %r0, 3448(%r12)
	std %r0, 3456(%r12)
	std %r0, 3464(%r12)
	std %r0, 3472(%r12)
	std %r0, 3480(%r12)
	std %r0, 3488(%r12)
	std %r0, 3496(%r12)
	std %r0, 3504(%r12)
	std %r0, 3512(%r12)
	std %r0, 3520(%r12)
	std %r0, 3528(%r12)
	std %r0, 3536(%r12)
	std %r0, 3544(%r12)
	std %r0, 3552(%r12)
	std %r0, 3560(%r12)
	std %r0, 3568(%r12)
	std %r0, 3576(%r12)
	std %r0, 3584(%r12)
	std %r0, 3592(%r12)
	std %r0, 3600(%r12)
	std %r0, 3608(%r12)
	addi %r1, %r1, 3648
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_rsa_pkcs1_encrypt_random:
	stdu %r1, -1216(%r1)
	addi %r12, %r1, 0
	std %r28, 144(%r12)
	std %r29, 152(%r12)
	std %r30, 160(%r12)
	std %r31, 168(%r12)
	mflr %r0
	std %r0, 176(%r12)
	or %r31, %r3, %r3
	or %r30, %r5, %r5
	or %r29, %r7, %r7
	ld %r0, 1312(%r12)
	subf %r28, %r0, %r7
	addi %r28, %r28, -3
	ld %r3, 1320(%r12)
	ld %r11, 1328(%r12)
	addi %r7, %r12, 192
	li %r4, 0
	li %r5, 0
	cmpldi %cr0, %r11, 0
	bne %cr0, 20f
	b 21f
20:
22:
	add %r12, %r3, %r4
	lbz %r0, 0(%r12)
	addi %r4, %r4, 1
	cmpldi %cr0, %r0, 0
	bne %cr0, 23f
	b 24f
23:
	add %r12, %r7, %r5
	stb %r0, 0(%r12)
	addi %r5, %r5, 1
24:
	subf %r12, %r5, %r28
	cmpldi %cr0, %r12, 0
	bne %cr0, 25f
	b 26f
25:
	subf %r12, %r4, %r11
26:
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
21:
	subf %r12, %r5, %r28
	cmpldi %cr0, %r12, 0
	beq %cr0, 27f
	or %r10, %r4, %r4
	or %r4, %r31, %r31
	or %r11, %r29, %r29
	li %r0, 0
29:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	addi %r12, %r1, 0
	addi %r4, %r12, 192
	or %r11, %r5, %r5
	cmpldi %cr0, %r11, 0
	bne %cr0, 210f
	b 211f
210:
212:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
211:
	addi %r12, %r28, 128
	subf %r0, %r10, %r12
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	li %r0, 0
	std %r0, 0(%r30)
	subf %r4, %r5, %r10
	addi %r4, %r4, -129
	rldicl %r4, %r4, 1, 63
	cmpldi %cr0, %r4, 0
	bne %cr0, 215f
	or %r0, %r12, %r12
	b 216f
215:
	add %r0, %r28, %r10
	subf %r0, %r5, %r0
216:
	std %r0, 8(%r30)
	li %r3, 0
	b 214f
213:
	std %r10, 0(%r30)
	li %r0, 0
	std %r0, 8(%r30)
	li %r3, 3
214:
	b 28f
27:
	std %r4, 0(%r30)
	li %r0, 0
	std %r0, 8(%r30)
	addi %r12, %r1, 0
	std %r7, 96(%r12)
	std %r28, 104(%r12)
	ld %r0, 1336(%r12)
	std %r0, 112(%r12)
	ld %r0, 1344(%r12)
	std %r0, 120(%r12)
	ld %r0, 1352(%r12)
	std %r0, 128(%r12)
	ld %r0, 1360(%r12)
	std %r0, 136(%r12)
	or %r3, %r31, %r31
	or %r4, %r29, %r29
	or %r5, %r6, %r6
	or %r6, %r29, %r29
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	or %r9, %r10, %r10
	ld %r10, 1312(%r12)
	bl {vg_rsa_pkcs1_encrypt_precomputed}
	li %r5, 2
	subf %r5, %r3, %r5
	addi %r12, %r1, 0
	addi %r4, %r12, 192
	or %r11, %r28, %r28
	li %r0, 0
217:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	or %r3, %r5, %r5
28:
	addi %r12, %r1, 0
	ld %r0, 176(%r12)
	mtlr %r0
	ld %r28, 144(%r12)
	ld %r29, 152(%r12)
	ld %r30, 160(%r12)
	ld %r31, 168(%r12)
	addi %r1, %r1, 1216
	li %r0, 0
	stdu %r1, -3440(%r1)
	addi %r12, %r1, 32
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
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	std %r0, 720(%r12)
	std %r0, 728(%r12)
	std %r0, 736(%r12)
	std %r0, 744(%r12)
	std %r0, 752(%r12)
	std %r0, 760(%r12)
	std %r0, 768(%r12)
	std %r0, 776(%r12)
	std %r0, 784(%r12)
	std %r0, 792(%r12)
	std %r0, 800(%r12)
	std %r0, 808(%r12)
	std %r0, 816(%r12)
	std %r0, 824(%r12)
	std %r0, 832(%r12)
	std %r0, 840(%r12)
	std %r0, 848(%r12)
	std %r0, 856(%r12)
	std %r0, 864(%r12)
	std %r0, 872(%r12)
	std %r0, 880(%r12)
	std %r0, 888(%r12)
	std %r0, 896(%r12)
	std %r0, 904(%r12)
	std %r0, 912(%r12)
	std %r0, 920(%r12)
	std %r0, 928(%r12)
	std %r0, 936(%r12)
	std %r0, 944(%r12)
	std %r0, 952(%r12)
	std %r0, 960(%r12)
	std %r0, 968(%r12)
	std %r0, 976(%r12)
	std %r0, 984(%r12)
	std %r0, 992(%r12)
	std %r0, 1000(%r12)
	std %r0, 1008(%r12)
	std %r0, 1016(%r12)
	std %r0, 1024(%r12)
	std %r0, 1032(%r12)
	std %r0, 1040(%r12)
	std %r0, 1048(%r12)
	std %r0, 1056(%r12)
	std %r0, 1064(%r12)
	std %r0, 1072(%r12)
	std %r0, 1080(%r12)
	std %r0, 1088(%r12)
	std %r0, 1096(%r12)
	std %r0, 1104(%r12)
	std %r0, 1112(%r12)
	std %r0, 1120(%r12)
	std %r0, 1128(%r12)
	std %r0, 1136(%r12)
	std %r0, 1144(%r12)
	std %r0, 1152(%r12)
	std %r0, 1160(%r12)
	std %r0, 1168(%r12)
	std %r0, 1176(%r12)
	std %r0, 1184(%r12)
	std %r0, 1192(%r12)
	std %r0, 1200(%r12)
	std %r0, 1208(%r12)
	std %r0, 1216(%r12)
	std %r0, 1224(%r12)
	std %r0, 1232(%r12)
	std %r0, 1240(%r12)
	std %r0, 1248(%r12)
	std %r0, 1256(%r12)
	std %r0, 1264(%r12)
	std %r0, 1272(%r12)
	std %r0, 1280(%r12)
	std %r0, 1288(%r12)
	std %r0, 1296(%r12)
	std %r0, 1304(%r12)
	std %r0, 1312(%r12)
	std %r0, 1320(%r12)
	std %r0, 1328(%r12)
	std %r0, 1336(%r12)
	std %r0, 1344(%r12)
	std %r0, 1352(%r12)
	std %r0, 1360(%r12)
	std %r0, 1368(%r12)
	std %r0, 1376(%r12)
	std %r0, 1384(%r12)
	std %r0, 1392(%r12)
	std %r0, 1400(%r12)
	std %r0, 1408(%r12)
	std %r0, 1416(%r12)
	std %r0, 1424(%r12)
	std %r0, 1432(%r12)
	std %r0, 1440(%r12)
	std %r0, 1448(%r12)
	std %r0, 1456(%r12)
	std %r0, 1464(%r12)
	std %r0, 1472(%r12)
	std %r0, 1480(%r12)
	std %r0, 1488(%r12)
	std %r0, 1496(%r12)
	std %r0, 1504(%r12)
	std %r0, 1512(%r12)
	std %r0, 1520(%r12)
	std %r0, 1528(%r12)
	std %r0, 1536(%r12)
	std %r0, 1544(%r12)
	std %r0, 1552(%r12)
	std %r0, 1560(%r12)
	std %r0, 1568(%r12)
	std %r0, 1576(%r12)
	std %r0, 1584(%r12)
	std %r0, 1592(%r12)
	std %r0, 1600(%r12)
	std %r0, 1608(%r12)
	std %r0, 1616(%r12)
	std %r0, 1624(%r12)
	std %r0, 1632(%r12)
	std %r0, 1640(%r12)
	std %r0, 1648(%r12)
	std %r0, 1656(%r12)
	std %r0, 1664(%r12)
	std %r0, 1672(%r12)
	std %r0, 1680(%r12)
	std %r0, 1688(%r12)
	std %r0, 1696(%r12)
	std %r0, 1704(%r12)
	std %r0, 1712(%r12)
	std %r0, 1720(%r12)
	std %r0, 1728(%r12)
	std %r0, 1736(%r12)
	std %r0, 1744(%r12)
	std %r0, 1752(%r12)
	std %r0, 1760(%r12)
	std %r0, 1768(%r12)
	std %r0, 1776(%r12)
	std %r0, 1784(%r12)
	std %r0, 1792(%r12)
	std %r0, 1800(%r12)
	std %r0, 1808(%r12)
	std %r0, 1816(%r12)
	std %r0, 1824(%r12)
	std %r0, 1832(%r12)
	std %r0, 1840(%r12)
	std %r0, 1848(%r12)
	std %r0, 1856(%r12)
	std %r0, 1864(%r12)
	std %r0, 1872(%r12)
	std %r0, 1880(%r12)
	std %r0, 1888(%r12)
	std %r0, 1896(%r12)
	std %r0, 1904(%r12)
	std %r0, 1912(%r12)
	std %r0, 1920(%r12)
	std %r0, 1928(%r12)
	std %r0, 1936(%r12)
	std %r0, 1944(%r12)
	std %r0, 1952(%r12)
	std %r0, 1960(%r12)
	std %r0, 1968(%r12)
	std %r0, 1976(%r12)
	std %r0, 1984(%r12)
	std %r0, 1992(%r12)
	std %r0, 2000(%r12)
	std %r0, 2008(%r12)
	std %r0, 2016(%r12)
	std %r0, 2024(%r12)
	std %r0, 2032(%r12)
	std %r0, 2040(%r12)
	std %r0, 2048(%r12)
	std %r0, 2056(%r12)
	std %r0, 2064(%r12)
	std %r0, 2072(%r12)
	std %r0, 2080(%r12)
	std %r0, 2088(%r12)
	std %r0, 2096(%r12)
	std %r0, 2104(%r12)
	std %r0, 2112(%r12)
	std %r0, 2120(%r12)
	std %r0, 2128(%r12)
	std %r0, 2136(%r12)
	std %r0, 2144(%r12)
	std %r0, 2152(%r12)
	std %r0, 2160(%r12)
	std %r0, 2168(%r12)
	std %r0, 2176(%r12)
	std %r0, 2184(%r12)
	std %r0, 2192(%r12)
	std %r0, 2200(%r12)
	std %r0, 2208(%r12)
	std %r0, 2216(%r12)
	std %r0, 2224(%r12)
	std %r0, 2232(%r12)
	std %r0, 2240(%r12)
	std %r0, 2248(%r12)
	std %r0, 2256(%r12)
	std %r0, 2264(%r12)
	std %r0, 2272(%r12)
	std %r0, 2280(%r12)
	std %r0, 2288(%r12)
	std %r0, 2296(%r12)
	std %r0, 2304(%r12)
	std %r0, 2312(%r12)
	std %r0, 2320(%r12)
	std %r0, 2328(%r12)
	std %r0, 2336(%r12)
	std %r0, 2344(%r12)
	std %r0, 2352(%r12)
	std %r0, 2360(%r12)
	std %r0, 2368(%r12)
	std %r0, 2376(%r12)
	std %r0, 2384(%r12)
	std %r0, 2392(%r12)
	std %r0, 2400(%r12)
	std %r0, 2408(%r12)
	std %r0, 2416(%r12)
	std %r0, 2424(%r12)
	std %r0, 2432(%r12)
	std %r0, 2440(%r12)
	std %r0, 2448(%r12)
	std %r0, 2456(%r12)
	std %r0, 2464(%r12)
	std %r0, 2472(%r12)
	std %r0, 2480(%r12)
	std %r0, 2488(%r12)
	std %r0, 2496(%r12)
	std %r0, 2504(%r12)
	std %r0, 2512(%r12)
	std %r0, 2520(%r12)
	std %r0, 2528(%r12)
	std %r0, 2536(%r12)
	std %r0, 2544(%r12)
	std %r0, 2552(%r12)
	std %r0, 2560(%r12)
	std %r0, 2568(%r12)
	std %r0, 2576(%r12)
	std %r0, 2584(%r12)
	std %r0, 2592(%r12)
	std %r0, 2600(%r12)
	std %r0, 2608(%r12)
	std %r0, 2616(%r12)
	std %r0, 2624(%r12)
	std %r0, 2632(%r12)
	std %r0, 2640(%r12)
	std %r0, 2648(%r12)
	std %r0, 2656(%r12)
	std %r0, 2664(%r12)
	std %r0, 2672(%r12)
	std %r0, 2680(%r12)
	std %r0, 2688(%r12)
	std %r0, 2696(%r12)
	std %r0, 2704(%r12)
	std %r0, 2712(%r12)
	std %r0, 2720(%r12)
	std %r0, 2728(%r12)
	std %r0, 2736(%r12)
	std %r0, 2744(%r12)
	std %r0, 2752(%r12)
	std %r0, 2760(%r12)
	std %r0, 2768(%r12)
	std %r0, 2776(%r12)
	std %r0, 2784(%r12)
	std %r0, 2792(%r12)
	std %r0, 2800(%r12)
	std %r0, 2808(%r12)
	std %r0, 2816(%r12)
	std %r0, 2824(%r12)
	std %r0, 2832(%r12)
	std %r0, 2840(%r12)
	std %r0, 2848(%r12)
	std %r0, 2856(%r12)
	std %r0, 2864(%r12)
	std %r0, 2872(%r12)
	std %r0, 2880(%r12)
	std %r0, 2888(%r12)
	std %r0, 2896(%r12)
	std %r0, 2904(%r12)
	std %r0, 2912(%r12)
	std %r0, 2920(%r12)
	std %r0, 2928(%r12)
	std %r0, 2936(%r12)
	std %r0, 2944(%r12)
	std %r0, 2952(%r12)
	std %r0, 2960(%r12)
	std %r0, 2968(%r12)
	std %r0, 2976(%r12)
	std %r0, 2984(%r12)
	std %r0, 2992(%r12)
	std %r0, 3000(%r12)
	std %r0, 3008(%r12)
	std %r0, 3016(%r12)
	std %r0, 3024(%r12)
	std %r0, 3032(%r12)
	std %r0, 3040(%r12)
	std %r0, 3048(%r12)
	std %r0, 3056(%r12)
	std %r0, 3064(%r12)
	std %r0, 3072(%r12)
	std %r0, 3080(%r12)
	std %r0, 3088(%r12)
	std %r0, 3096(%r12)
	std %r0, 3104(%r12)
	std %r0, 3112(%r12)
	std %r0, 3120(%r12)
	std %r0, 3128(%r12)
	std %r0, 3136(%r12)
	std %r0, 3144(%r12)
	std %r0, 3152(%r12)
	std %r0, 3160(%r12)
	std %r0, 3168(%r12)
	std %r0, 3176(%r12)
	std %r0, 3184(%r12)
	std %r0, 3192(%r12)
	std %r0, 3200(%r12)
	std %r0, 3208(%r12)
	std %r0, 3216(%r12)
	std %r0, 3224(%r12)
	std %r0, 3232(%r12)
	std %r0, 3240(%r12)
	std %r0, 3248(%r12)
	std %r0, 3256(%r12)
	std %r0, 3264(%r12)
	std %r0, 3272(%r12)
	std %r0, 3280(%r12)
	std %r0, 3288(%r12)
	std %r0, 3296(%r12)
	std %r0, 3304(%r12)
	std %r0, 3312(%r12)
	std %r0, 3320(%r12)
	std %r0, 3328(%r12)
	std %r0, 3336(%r12)
	std %r0, 3344(%r12)
	std %r0, 3352(%r12)
	std %r0, 3360(%r12)
	std %r0, 3368(%r12)
	std %r0, 3376(%r12)
	std %r0, 3384(%r12)
	std %r0, 3392(%r12)
	std %r0, 3400(%r12)
	addi %r1, %r1, 3440
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	blr
