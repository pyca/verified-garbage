// The functions of `src/triple_des_cfb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cfb64_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -944
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	addi t0, s4, 560
	addi t2, a0, 0
	addi t4, zero, 384
20:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 20b
	andi t0, s2, 3
	beqz t0, 21f
	beqz s3, 23f
25:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
26:
	addi t6, a6, -3
	beqz t6, 27f
	addi t6, a6, -2
	beqz t6, 29f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 210f
29:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
210:
	j 28f
27:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
28:
211:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 211b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 26b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 25b
	j 24f
23:
24:
	j 22f
21:
	beqz s3, 212f
214:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
215:
	addi t6, a6, -3
	beqz t6, 216f
	addi t6, a6, -2
	beqz t6, 218f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 219f
218:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
219:
	j 217f
216:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
217:
220:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 220b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 215b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 214b
	j 213f
212:
213:
22:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 118
221:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 221b
	addi sp, sp, 944
	ret
	.option pop

vg_triple_des_cfb64_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1120
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_prepare}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 20f
	srli t0, s3, 6
	beqz t0, 22f
24:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 176(s4)
	lwu t0, 36(s4)
	sw t0, 180(s4)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 184(s4)
	lwu t0, 36(s4)
	sw t0, 188(s4)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 192(s4)
	lwu t0, 36(s4)
	sw t0, 196(s4)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 200(s4)
	lwu t0, 36(s4)
	sw t0, 204(s4)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 208(s4)
	lwu t0, 36(s4)
	sw t0, 212(s4)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 216(s4)
	lwu t0, 36(s4)
	sw t0, 220(s4)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 224(s4)
	lwu t0, 36(s4)
	sw t0, 228(s4)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 232(s4)
	lwu t0, 36(s4)
	sw t0, 236(s4)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 240(s4)
	lwu t0, 36(s4)
	sw t0, 244(s4)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 248(s4)
	lwu t0, 36(s4)
	sw t0, 252(s4)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 256(s4)
	lwu t0, 36(s4)
	sw t0, 260(s4)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 264(s4)
	lwu t0, 36(s4)
	sw t0, 268(s4)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 272(s4)
	lwu t0, 36(s4)
	sw t0, 276(s4)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 280(s4)
	lwu t0, 36(s4)
	sw t0, 284(s4)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 288(s4)
	lwu t0, 36(s4)
	sw t0, 292(s4)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 296(s4)
	lwu t0, 36(s4)
	sw t0, 300(s4)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 304(s4)
	lwu t0, 36(s4)
	sw t0, 308(s4)
	lbu t0, 256(s2)
	lbu t2, 257(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 258(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 259(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 260(s2)
	lbu t2, 261(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 262(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 263(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 312(s4)
	lwu t0, 36(s4)
	sw t0, 316(s4)
	lbu t0, 264(s2)
	lbu t2, 265(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 266(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 267(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 268(s2)
	lbu t2, 269(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 270(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 271(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 320(s4)
	lwu t0, 36(s4)
	sw t0, 324(s4)
	lbu t0, 272(s2)
	lbu t2, 273(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 274(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 275(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 276(s2)
	lbu t2, 277(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 278(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 279(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 328(s4)
	lwu t0, 36(s4)
	sw t0, 332(s4)
	lbu t0, 280(s2)
	lbu t2, 281(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 282(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 283(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 284(s2)
	lbu t2, 285(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 286(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 287(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 336(s4)
	lwu t0, 36(s4)
	sw t0, 340(s4)
	lbu t0, 288(s2)
	lbu t2, 289(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 290(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 291(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 292(s2)
	lbu t2, 293(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 294(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 295(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 344(s4)
	lwu t0, 36(s4)
	sw t0, 348(s4)
	lbu t0, 296(s2)
	lbu t2, 297(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 298(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 299(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 300(s2)
	lbu t2, 301(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 302(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 303(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 352(s4)
	lwu t0, 36(s4)
	sw t0, 356(s4)
	lbu t0, 304(s2)
	lbu t2, 305(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 306(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 307(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 308(s2)
	lbu t2, 309(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 310(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 311(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 360(s4)
	lwu t0, 36(s4)
	sw t0, 364(s4)
	lbu t0, 312(s2)
	lbu t2, 313(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 314(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 315(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 316(s2)
	lbu t2, 317(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 318(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 319(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 368(s4)
	lwu t0, 36(s4)
	sw t0, 372(s4)
	lbu t0, 320(s2)
	lbu t2, 321(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 322(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 323(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 324(s2)
	lbu t2, 325(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 326(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 327(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 376(s4)
	lwu t0, 36(s4)
	sw t0, 380(s4)
	lbu t0, 328(s2)
	lbu t2, 329(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 330(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 331(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 332(s2)
	lbu t2, 333(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 334(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 335(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 384(s4)
	lwu t0, 36(s4)
	sw t0, 388(s4)
	lbu t0, 336(s2)
	lbu t2, 337(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 338(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 339(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 340(s2)
	lbu t2, 341(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 342(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 343(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 392(s4)
	lwu t0, 36(s4)
	sw t0, 396(s4)
	lbu t0, 344(s2)
	lbu t2, 345(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 346(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 347(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 348(s2)
	lbu t2, 349(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 350(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 351(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 400(s4)
	lwu t0, 36(s4)
	sw t0, 404(s4)
	lbu t0, 352(s2)
	lbu t2, 353(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 354(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 355(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 356(s2)
	lbu t2, 357(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 358(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 359(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 408(s4)
	lwu t0, 36(s4)
	sw t0, 412(s4)
	lbu t0, 360(s2)
	lbu t2, 361(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 362(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 363(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 364(s2)
	lbu t2, 365(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 366(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 367(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 416(s4)
	lwu t0, 36(s4)
	sw t0, 420(s4)
	lbu t0, 368(s2)
	lbu t2, 369(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 370(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 371(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 372(s2)
	lbu t2, 373(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 374(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 375(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 424(s4)
	lwu t0, 36(s4)
	sw t0, 428(s4)
	lbu t0, 376(s2)
	lbu t2, 377(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 378(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 379(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 380(s2)
	lbu t2, 381(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 382(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 383(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 432(s4)
	lwu t0, 36(s4)
	sw t0, 436(s4)
	lbu t0, 384(s2)
	lbu t2, 385(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 386(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 387(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 388(s2)
	lbu t2, 389(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 390(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 391(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 440(s4)
	lwu t0, 36(s4)
	sw t0, 444(s4)
	lbu t0, 392(s2)
	lbu t2, 393(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 394(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 395(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 396(s2)
	lbu t2, 397(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 398(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 399(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 448(s4)
	lwu t0, 36(s4)
	sw t0, 452(s4)
	lbu t0, 400(s2)
	lbu t2, 401(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 402(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 403(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 404(s2)
	lbu t2, 405(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 406(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 407(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 456(s4)
	lwu t0, 36(s4)
	sw t0, 460(s4)
	lbu t0, 408(s2)
	lbu t2, 409(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 410(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 411(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 412(s2)
	lbu t2, 413(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 414(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 415(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 464(s4)
	lwu t0, 36(s4)
	sw t0, 468(s4)
	lbu t0, 416(s2)
	lbu t2, 417(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 418(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 419(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 420(s2)
	lbu t2, 421(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 422(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 423(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 472(s4)
	lwu t0, 36(s4)
	sw t0, 476(s4)
	lbu t0, 424(s2)
	lbu t2, 425(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 426(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 427(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 428(s2)
	lbu t2, 429(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 430(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 431(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 480(s4)
	lwu t0, 36(s4)
	sw t0, 484(s4)
	lbu t0, 432(s2)
	lbu t2, 433(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 434(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 435(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 436(s2)
	lbu t2, 437(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 438(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 439(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 488(s4)
	lwu t0, 36(s4)
	sw t0, 492(s4)
	lbu t0, 440(s2)
	lbu t2, 441(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 442(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 443(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 444(s2)
	lbu t2, 445(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 446(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 447(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 496(s4)
	lwu t0, 36(s4)
	sw t0, 500(s4)
	lbu t0, 448(s2)
	lbu t2, 449(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 450(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 451(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 452(s2)
	lbu t2, 453(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 454(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 455(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 504(s4)
	lwu t0, 36(s4)
	sw t0, 508(s4)
	lbu t0, 456(s2)
	lbu t2, 457(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 458(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 459(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 460(s2)
	lbu t2, 461(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 462(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 463(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 512(s4)
	lwu t0, 36(s4)
	sw t0, 516(s4)
	lbu t0, 464(s2)
	lbu t2, 465(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 466(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 467(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 468(s2)
	lbu t2, 469(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 470(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 471(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 520(s4)
	lwu t0, 36(s4)
	sw t0, 524(s4)
	lbu t0, 472(s2)
	lbu t2, 473(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 474(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 475(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 476(s2)
	lbu t2, 477(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 478(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 479(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 528(s4)
	lwu t0, 36(s4)
	sw t0, 532(s4)
	lbu t0, 480(s2)
	lbu t2, 481(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 482(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 483(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 484(s2)
	lbu t2, 485(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 486(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 487(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 536(s4)
	lwu t0, 36(s4)
	sw t0, 540(s4)
	lbu t0, 488(s2)
	lbu t2, 489(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 490(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 491(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 492(s2)
	lbu t2, 493(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 494(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 495(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 544(s4)
	lwu t0, 36(s4)
	sw t0, 548(s4)
	lbu t0, 496(s2)
	lbu t2, 497(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 498(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 499(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 500(s2)
	lbu t2, 501(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 502(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 503(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 552(s4)
	lwu t0, 36(s4)
	sw t0, 556(s4)
	lbu t0, 504(s2)
	lbu t2, 505(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 506(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 507(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 508(s2)
	lbu t2, 509(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 510(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 511(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 64(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 68(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 72(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 76(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 80(s4)
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 84(s4)
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 88(s4)
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 92(s4)
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 96(s4)
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 100(s4)
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 104(s4)
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 108(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 112(s4)
	xor t0, t0, t1
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 116(s4)
	xor t0, t0, t1
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 120(s4)
	xor t0, t0, t1
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 124(s4)
	xor t0, t0, t1
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 128(s4)
	xor t0, t0, t1
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 132(s4)
	xor t0, t0, t1
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 136(s4)
	xor t0, t0, t1
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 140(s4)
	xor t0, t0, t1
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 144(s4)
	xor t0, t0, t1
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 148(s4)
	xor t0, t0, t1
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 152(s4)
	xor t0, t0, t1
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 156(s4)
	xor t0, t0, t1
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 160(s4)
	xor t0, t0, t1
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 164(s4)
	xor t0, t0, t1
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 168(s4)
	xor t0, t0, t1
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 172(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 176(s4)
	xor t0, t0, t1
	sb t0, 128(s2)
	srli t2, t0, 8
	sb t2, 129(s2)
	srli t2, t0, 16
	sb t2, 130(s2)
	srli t2, t0, 24
	sb t2, 131(s2)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 180(s4)
	xor t0, t0, t1
	sb t0, 132(s2)
	srli t2, t0, 8
	sb t2, 133(s2)
	srli t2, t0, 16
	sb t2, 134(s2)
	srli t2, t0, 24
	sb t2, 135(s2)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 184(s4)
	xor t0, t0, t1
	sb t0, 136(s2)
	srli t2, t0, 8
	sb t2, 137(s2)
	srli t2, t0, 16
	sb t2, 138(s2)
	srli t2, t0, 24
	sb t2, 139(s2)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 188(s4)
	xor t0, t0, t1
	sb t0, 140(s2)
	srli t2, t0, 8
	sb t2, 141(s2)
	srli t2, t0, 16
	sb t2, 142(s2)
	srli t2, t0, 24
	sb t2, 143(s2)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 192(s4)
	xor t0, t0, t1
	sb t0, 144(s2)
	srli t2, t0, 8
	sb t2, 145(s2)
	srli t2, t0, 16
	sb t2, 146(s2)
	srli t2, t0, 24
	sb t2, 147(s2)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 196(s4)
	xor t0, t0, t1
	sb t0, 148(s2)
	srli t2, t0, 8
	sb t2, 149(s2)
	srli t2, t0, 16
	sb t2, 150(s2)
	srli t2, t0, 24
	sb t2, 151(s2)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 200(s4)
	xor t0, t0, t1
	sb t0, 152(s2)
	srli t2, t0, 8
	sb t2, 153(s2)
	srli t2, t0, 16
	sb t2, 154(s2)
	srli t2, t0, 24
	sb t2, 155(s2)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 204(s4)
	xor t0, t0, t1
	sb t0, 156(s2)
	srli t2, t0, 8
	sb t2, 157(s2)
	srli t2, t0, 16
	sb t2, 158(s2)
	srli t2, t0, 24
	sb t2, 159(s2)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 208(s4)
	xor t0, t0, t1
	sb t0, 160(s2)
	srli t2, t0, 8
	sb t2, 161(s2)
	srli t2, t0, 16
	sb t2, 162(s2)
	srli t2, t0, 24
	sb t2, 163(s2)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 212(s4)
	xor t0, t0, t1
	sb t0, 164(s2)
	srli t2, t0, 8
	sb t2, 165(s2)
	srli t2, t0, 16
	sb t2, 166(s2)
	srli t2, t0, 24
	sb t2, 167(s2)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 216(s4)
	xor t0, t0, t1
	sb t0, 168(s2)
	srli t2, t0, 8
	sb t2, 169(s2)
	srli t2, t0, 16
	sb t2, 170(s2)
	srli t2, t0, 24
	sb t2, 171(s2)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 220(s4)
	xor t0, t0, t1
	sb t0, 172(s2)
	srli t2, t0, 8
	sb t2, 173(s2)
	srli t2, t0, 16
	sb t2, 174(s2)
	srli t2, t0, 24
	sb t2, 175(s2)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 224(s4)
	xor t0, t0, t1
	sb t0, 176(s2)
	srli t2, t0, 8
	sb t2, 177(s2)
	srli t2, t0, 16
	sb t2, 178(s2)
	srli t2, t0, 24
	sb t2, 179(s2)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 228(s4)
	xor t0, t0, t1
	sb t0, 180(s2)
	srli t2, t0, 8
	sb t2, 181(s2)
	srli t2, t0, 16
	sb t2, 182(s2)
	srli t2, t0, 24
	sb t2, 183(s2)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 232(s4)
	xor t0, t0, t1
	sb t0, 184(s2)
	srli t2, t0, 8
	sb t2, 185(s2)
	srli t2, t0, 16
	sb t2, 186(s2)
	srli t2, t0, 24
	sb t2, 187(s2)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 236(s4)
	xor t0, t0, t1
	sb t0, 188(s2)
	srli t2, t0, 8
	sb t2, 189(s2)
	srli t2, t0, 16
	sb t2, 190(s2)
	srli t2, t0, 24
	sb t2, 191(s2)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 240(s4)
	xor t0, t0, t1
	sb t0, 192(s2)
	srli t2, t0, 8
	sb t2, 193(s2)
	srli t2, t0, 16
	sb t2, 194(s2)
	srli t2, t0, 24
	sb t2, 195(s2)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 244(s4)
	xor t0, t0, t1
	sb t0, 196(s2)
	srli t2, t0, 8
	sb t2, 197(s2)
	srli t2, t0, 16
	sb t2, 198(s2)
	srli t2, t0, 24
	sb t2, 199(s2)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 248(s4)
	xor t0, t0, t1
	sb t0, 200(s2)
	srli t2, t0, 8
	sb t2, 201(s2)
	srli t2, t0, 16
	sb t2, 202(s2)
	srli t2, t0, 24
	sb t2, 203(s2)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 252(s4)
	xor t0, t0, t1
	sb t0, 204(s2)
	srli t2, t0, 8
	sb t2, 205(s2)
	srli t2, t0, 16
	sb t2, 206(s2)
	srli t2, t0, 24
	sb t2, 207(s2)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 256(s4)
	xor t0, t0, t1
	sb t0, 208(s2)
	srli t2, t0, 8
	sb t2, 209(s2)
	srli t2, t0, 16
	sb t2, 210(s2)
	srli t2, t0, 24
	sb t2, 211(s2)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 260(s4)
	xor t0, t0, t1
	sb t0, 212(s2)
	srli t2, t0, 8
	sb t2, 213(s2)
	srli t2, t0, 16
	sb t2, 214(s2)
	srli t2, t0, 24
	sb t2, 215(s2)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 264(s4)
	xor t0, t0, t1
	sb t0, 216(s2)
	srli t2, t0, 8
	sb t2, 217(s2)
	srli t2, t0, 16
	sb t2, 218(s2)
	srli t2, t0, 24
	sb t2, 219(s2)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 268(s4)
	xor t0, t0, t1
	sb t0, 220(s2)
	srli t2, t0, 8
	sb t2, 221(s2)
	srli t2, t0, 16
	sb t2, 222(s2)
	srli t2, t0, 24
	sb t2, 223(s2)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 272(s4)
	xor t0, t0, t1
	sb t0, 224(s2)
	srli t2, t0, 8
	sb t2, 225(s2)
	srli t2, t0, 16
	sb t2, 226(s2)
	srli t2, t0, 24
	sb t2, 227(s2)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 276(s4)
	xor t0, t0, t1
	sb t0, 228(s2)
	srli t2, t0, 8
	sb t2, 229(s2)
	srli t2, t0, 16
	sb t2, 230(s2)
	srli t2, t0, 24
	sb t2, 231(s2)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 280(s4)
	xor t0, t0, t1
	sb t0, 232(s2)
	srli t2, t0, 8
	sb t2, 233(s2)
	srli t2, t0, 16
	sb t2, 234(s2)
	srli t2, t0, 24
	sb t2, 235(s2)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 284(s4)
	xor t0, t0, t1
	sb t0, 236(s2)
	srli t2, t0, 8
	sb t2, 237(s2)
	srli t2, t0, 16
	sb t2, 238(s2)
	srli t2, t0, 24
	sb t2, 239(s2)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 288(s4)
	xor t0, t0, t1
	sb t0, 240(s2)
	srli t2, t0, 8
	sb t2, 241(s2)
	srli t2, t0, 16
	sb t2, 242(s2)
	srli t2, t0, 24
	sb t2, 243(s2)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 292(s4)
	xor t0, t0, t1
	sb t0, 244(s2)
	srli t2, t0, 8
	sb t2, 245(s2)
	srli t2, t0, 16
	sb t2, 246(s2)
	srli t2, t0, 24
	sb t2, 247(s2)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 296(s4)
	xor t0, t0, t1
	sb t0, 248(s2)
	srli t2, t0, 8
	sb t2, 249(s2)
	srli t2, t0, 16
	sb t2, 250(s2)
	srli t2, t0, 24
	sb t2, 251(s2)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 300(s4)
	xor t0, t0, t1
	sb t0, 252(s2)
	srli t2, t0, 8
	sb t2, 253(s2)
	srli t2, t0, 16
	sb t2, 254(s2)
	srli t2, t0, 24
	sb t2, 255(s2)
	lbu t0, 256(s2)
	lbu t2, 257(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 258(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 259(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 304(s4)
	xor t0, t0, t1
	sb t0, 256(s2)
	srli t2, t0, 8
	sb t2, 257(s2)
	srli t2, t0, 16
	sb t2, 258(s2)
	srli t2, t0, 24
	sb t2, 259(s2)
	lbu t0, 260(s2)
	lbu t2, 261(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 262(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 263(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 308(s4)
	xor t0, t0, t1
	sb t0, 260(s2)
	srli t2, t0, 8
	sb t2, 261(s2)
	srli t2, t0, 16
	sb t2, 262(s2)
	srli t2, t0, 24
	sb t2, 263(s2)
	lbu t0, 264(s2)
	lbu t2, 265(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 266(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 267(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 312(s4)
	xor t0, t0, t1
	sb t0, 264(s2)
	srli t2, t0, 8
	sb t2, 265(s2)
	srli t2, t0, 16
	sb t2, 266(s2)
	srli t2, t0, 24
	sb t2, 267(s2)
	lbu t0, 268(s2)
	lbu t2, 269(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 270(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 271(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 316(s4)
	xor t0, t0, t1
	sb t0, 268(s2)
	srli t2, t0, 8
	sb t2, 269(s2)
	srli t2, t0, 16
	sb t2, 270(s2)
	srli t2, t0, 24
	sb t2, 271(s2)
	lbu t0, 272(s2)
	lbu t2, 273(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 274(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 275(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 320(s4)
	xor t0, t0, t1
	sb t0, 272(s2)
	srli t2, t0, 8
	sb t2, 273(s2)
	srli t2, t0, 16
	sb t2, 274(s2)
	srli t2, t0, 24
	sb t2, 275(s2)
	lbu t0, 276(s2)
	lbu t2, 277(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 278(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 279(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 324(s4)
	xor t0, t0, t1
	sb t0, 276(s2)
	srli t2, t0, 8
	sb t2, 277(s2)
	srli t2, t0, 16
	sb t2, 278(s2)
	srli t2, t0, 24
	sb t2, 279(s2)
	lbu t0, 280(s2)
	lbu t2, 281(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 282(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 283(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 328(s4)
	xor t0, t0, t1
	sb t0, 280(s2)
	srli t2, t0, 8
	sb t2, 281(s2)
	srli t2, t0, 16
	sb t2, 282(s2)
	srli t2, t0, 24
	sb t2, 283(s2)
	lbu t0, 284(s2)
	lbu t2, 285(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 286(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 287(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 332(s4)
	xor t0, t0, t1
	sb t0, 284(s2)
	srli t2, t0, 8
	sb t2, 285(s2)
	srli t2, t0, 16
	sb t2, 286(s2)
	srli t2, t0, 24
	sb t2, 287(s2)
	lbu t0, 288(s2)
	lbu t2, 289(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 290(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 291(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 336(s4)
	xor t0, t0, t1
	sb t0, 288(s2)
	srli t2, t0, 8
	sb t2, 289(s2)
	srli t2, t0, 16
	sb t2, 290(s2)
	srli t2, t0, 24
	sb t2, 291(s2)
	lbu t0, 292(s2)
	lbu t2, 293(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 294(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 295(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 340(s4)
	xor t0, t0, t1
	sb t0, 292(s2)
	srli t2, t0, 8
	sb t2, 293(s2)
	srli t2, t0, 16
	sb t2, 294(s2)
	srli t2, t0, 24
	sb t2, 295(s2)
	lbu t0, 296(s2)
	lbu t2, 297(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 298(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 299(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 344(s4)
	xor t0, t0, t1
	sb t0, 296(s2)
	srli t2, t0, 8
	sb t2, 297(s2)
	srli t2, t0, 16
	sb t2, 298(s2)
	srli t2, t0, 24
	sb t2, 299(s2)
	lbu t0, 300(s2)
	lbu t2, 301(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 302(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 303(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 348(s4)
	xor t0, t0, t1
	sb t0, 300(s2)
	srli t2, t0, 8
	sb t2, 301(s2)
	srli t2, t0, 16
	sb t2, 302(s2)
	srli t2, t0, 24
	sb t2, 303(s2)
	lbu t0, 304(s2)
	lbu t2, 305(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 306(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 307(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 352(s4)
	xor t0, t0, t1
	sb t0, 304(s2)
	srli t2, t0, 8
	sb t2, 305(s2)
	srli t2, t0, 16
	sb t2, 306(s2)
	srli t2, t0, 24
	sb t2, 307(s2)
	lbu t0, 308(s2)
	lbu t2, 309(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 310(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 311(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 356(s4)
	xor t0, t0, t1
	sb t0, 308(s2)
	srli t2, t0, 8
	sb t2, 309(s2)
	srli t2, t0, 16
	sb t2, 310(s2)
	srli t2, t0, 24
	sb t2, 311(s2)
	lbu t0, 312(s2)
	lbu t2, 313(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 314(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 315(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 360(s4)
	xor t0, t0, t1
	sb t0, 312(s2)
	srli t2, t0, 8
	sb t2, 313(s2)
	srli t2, t0, 16
	sb t2, 314(s2)
	srli t2, t0, 24
	sb t2, 315(s2)
	lbu t0, 316(s2)
	lbu t2, 317(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 318(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 319(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 364(s4)
	xor t0, t0, t1
	sb t0, 316(s2)
	srli t2, t0, 8
	sb t2, 317(s2)
	srli t2, t0, 16
	sb t2, 318(s2)
	srli t2, t0, 24
	sb t2, 319(s2)
	lbu t0, 320(s2)
	lbu t2, 321(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 322(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 323(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 368(s4)
	xor t0, t0, t1
	sb t0, 320(s2)
	srli t2, t0, 8
	sb t2, 321(s2)
	srli t2, t0, 16
	sb t2, 322(s2)
	srli t2, t0, 24
	sb t2, 323(s2)
	lbu t0, 324(s2)
	lbu t2, 325(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 326(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 327(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 372(s4)
	xor t0, t0, t1
	sb t0, 324(s2)
	srli t2, t0, 8
	sb t2, 325(s2)
	srli t2, t0, 16
	sb t2, 326(s2)
	srli t2, t0, 24
	sb t2, 327(s2)
	lbu t0, 328(s2)
	lbu t2, 329(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 330(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 331(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 376(s4)
	xor t0, t0, t1
	sb t0, 328(s2)
	srli t2, t0, 8
	sb t2, 329(s2)
	srli t2, t0, 16
	sb t2, 330(s2)
	srli t2, t0, 24
	sb t2, 331(s2)
	lbu t0, 332(s2)
	lbu t2, 333(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 334(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 335(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 380(s4)
	xor t0, t0, t1
	sb t0, 332(s2)
	srli t2, t0, 8
	sb t2, 333(s2)
	srli t2, t0, 16
	sb t2, 334(s2)
	srli t2, t0, 24
	sb t2, 335(s2)
	lbu t0, 336(s2)
	lbu t2, 337(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 338(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 339(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 384(s4)
	xor t0, t0, t1
	sb t0, 336(s2)
	srli t2, t0, 8
	sb t2, 337(s2)
	srli t2, t0, 16
	sb t2, 338(s2)
	srli t2, t0, 24
	sb t2, 339(s2)
	lbu t0, 340(s2)
	lbu t2, 341(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 342(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 343(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 388(s4)
	xor t0, t0, t1
	sb t0, 340(s2)
	srli t2, t0, 8
	sb t2, 341(s2)
	srli t2, t0, 16
	sb t2, 342(s2)
	srli t2, t0, 24
	sb t2, 343(s2)
	lbu t0, 344(s2)
	lbu t2, 345(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 346(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 347(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 392(s4)
	xor t0, t0, t1
	sb t0, 344(s2)
	srli t2, t0, 8
	sb t2, 345(s2)
	srli t2, t0, 16
	sb t2, 346(s2)
	srli t2, t0, 24
	sb t2, 347(s2)
	lbu t0, 348(s2)
	lbu t2, 349(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 350(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 351(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 396(s4)
	xor t0, t0, t1
	sb t0, 348(s2)
	srli t2, t0, 8
	sb t2, 349(s2)
	srli t2, t0, 16
	sb t2, 350(s2)
	srli t2, t0, 24
	sb t2, 351(s2)
	lbu t0, 352(s2)
	lbu t2, 353(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 354(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 355(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 400(s4)
	xor t0, t0, t1
	sb t0, 352(s2)
	srli t2, t0, 8
	sb t2, 353(s2)
	srli t2, t0, 16
	sb t2, 354(s2)
	srli t2, t0, 24
	sb t2, 355(s2)
	lbu t0, 356(s2)
	lbu t2, 357(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 358(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 359(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 404(s4)
	xor t0, t0, t1
	sb t0, 356(s2)
	srli t2, t0, 8
	sb t2, 357(s2)
	srli t2, t0, 16
	sb t2, 358(s2)
	srli t2, t0, 24
	sb t2, 359(s2)
	lbu t0, 360(s2)
	lbu t2, 361(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 362(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 363(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 408(s4)
	xor t0, t0, t1
	sb t0, 360(s2)
	srli t2, t0, 8
	sb t2, 361(s2)
	srli t2, t0, 16
	sb t2, 362(s2)
	srli t2, t0, 24
	sb t2, 363(s2)
	lbu t0, 364(s2)
	lbu t2, 365(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 366(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 367(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 412(s4)
	xor t0, t0, t1
	sb t0, 364(s2)
	srli t2, t0, 8
	sb t2, 365(s2)
	srli t2, t0, 16
	sb t2, 366(s2)
	srli t2, t0, 24
	sb t2, 367(s2)
	lbu t0, 368(s2)
	lbu t2, 369(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 370(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 371(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 416(s4)
	xor t0, t0, t1
	sb t0, 368(s2)
	srli t2, t0, 8
	sb t2, 369(s2)
	srli t2, t0, 16
	sb t2, 370(s2)
	srli t2, t0, 24
	sb t2, 371(s2)
	lbu t0, 372(s2)
	lbu t2, 373(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 374(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 375(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 420(s4)
	xor t0, t0, t1
	sb t0, 372(s2)
	srli t2, t0, 8
	sb t2, 373(s2)
	srli t2, t0, 16
	sb t2, 374(s2)
	srli t2, t0, 24
	sb t2, 375(s2)
	lbu t0, 376(s2)
	lbu t2, 377(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 378(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 379(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 424(s4)
	xor t0, t0, t1
	sb t0, 376(s2)
	srli t2, t0, 8
	sb t2, 377(s2)
	srli t2, t0, 16
	sb t2, 378(s2)
	srli t2, t0, 24
	sb t2, 379(s2)
	lbu t0, 380(s2)
	lbu t2, 381(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 382(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 383(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 428(s4)
	xor t0, t0, t1
	sb t0, 380(s2)
	srli t2, t0, 8
	sb t2, 381(s2)
	srli t2, t0, 16
	sb t2, 382(s2)
	srli t2, t0, 24
	sb t2, 383(s2)
	lbu t0, 384(s2)
	lbu t2, 385(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 386(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 387(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 432(s4)
	xor t0, t0, t1
	sb t0, 384(s2)
	srli t2, t0, 8
	sb t2, 385(s2)
	srli t2, t0, 16
	sb t2, 386(s2)
	srli t2, t0, 24
	sb t2, 387(s2)
	lbu t0, 388(s2)
	lbu t2, 389(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 390(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 391(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 436(s4)
	xor t0, t0, t1
	sb t0, 388(s2)
	srli t2, t0, 8
	sb t2, 389(s2)
	srli t2, t0, 16
	sb t2, 390(s2)
	srli t2, t0, 24
	sb t2, 391(s2)
	lbu t0, 392(s2)
	lbu t2, 393(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 394(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 395(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 440(s4)
	xor t0, t0, t1
	sb t0, 392(s2)
	srli t2, t0, 8
	sb t2, 393(s2)
	srli t2, t0, 16
	sb t2, 394(s2)
	srli t2, t0, 24
	sb t2, 395(s2)
	lbu t0, 396(s2)
	lbu t2, 397(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 398(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 399(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 444(s4)
	xor t0, t0, t1
	sb t0, 396(s2)
	srli t2, t0, 8
	sb t2, 397(s2)
	srli t2, t0, 16
	sb t2, 398(s2)
	srli t2, t0, 24
	sb t2, 399(s2)
	lbu t0, 400(s2)
	lbu t2, 401(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 402(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 403(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 448(s4)
	xor t0, t0, t1
	sb t0, 400(s2)
	srli t2, t0, 8
	sb t2, 401(s2)
	srli t2, t0, 16
	sb t2, 402(s2)
	srli t2, t0, 24
	sb t2, 403(s2)
	lbu t0, 404(s2)
	lbu t2, 405(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 406(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 407(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 452(s4)
	xor t0, t0, t1
	sb t0, 404(s2)
	srli t2, t0, 8
	sb t2, 405(s2)
	srli t2, t0, 16
	sb t2, 406(s2)
	srli t2, t0, 24
	sb t2, 407(s2)
	lbu t0, 408(s2)
	lbu t2, 409(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 410(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 411(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 456(s4)
	xor t0, t0, t1
	sb t0, 408(s2)
	srli t2, t0, 8
	sb t2, 409(s2)
	srli t2, t0, 16
	sb t2, 410(s2)
	srli t2, t0, 24
	sb t2, 411(s2)
	lbu t0, 412(s2)
	lbu t2, 413(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 414(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 415(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 460(s4)
	xor t0, t0, t1
	sb t0, 412(s2)
	srli t2, t0, 8
	sb t2, 413(s2)
	srli t2, t0, 16
	sb t2, 414(s2)
	srli t2, t0, 24
	sb t2, 415(s2)
	lbu t0, 416(s2)
	lbu t2, 417(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 418(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 419(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 464(s4)
	xor t0, t0, t1
	sb t0, 416(s2)
	srli t2, t0, 8
	sb t2, 417(s2)
	srli t2, t0, 16
	sb t2, 418(s2)
	srli t2, t0, 24
	sb t2, 419(s2)
	lbu t0, 420(s2)
	lbu t2, 421(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 422(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 423(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 468(s4)
	xor t0, t0, t1
	sb t0, 420(s2)
	srli t2, t0, 8
	sb t2, 421(s2)
	srli t2, t0, 16
	sb t2, 422(s2)
	srli t2, t0, 24
	sb t2, 423(s2)
	lbu t0, 424(s2)
	lbu t2, 425(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 426(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 427(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 472(s4)
	xor t0, t0, t1
	sb t0, 424(s2)
	srli t2, t0, 8
	sb t2, 425(s2)
	srli t2, t0, 16
	sb t2, 426(s2)
	srli t2, t0, 24
	sb t2, 427(s2)
	lbu t0, 428(s2)
	lbu t2, 429(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 430(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 431(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 476(s4)
	xor t0, t0, t1
	sb t0, 428(s2)
	srli t2, t0, 8
	sb t2, 429(s2)
	srli t2, t0, 16
	sb t2, 430(s2)
	srli t2, t0, 24
	sb t2, 431(s2)
	lbu t0, 432(s2)
	lbu t2, 433(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 434(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 435(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 480(s4)
	xor t0, t0, t1
	sb t0, 432(s2)
	srli t2, t0, 8
	sb t2, 433(s2)
	srli t2, t0, 16
	sb t2, 434(s2)
	srli t2, t0, 24
	sb t2, 435(s2)
	lbu t0, 436(s2)
	lbu t2, 437(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 438(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 439(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 484(s4)
	xor t0, t0, t1
	sb t0, 436(s2)
	srli t2, t0, 8
	sb t2, 437(s2)
	srli t2, t0, 16
	sb t2, 438(s2)
	srli t2, t0, 24
	sb t2, 439(s2)
	lbu t0, 440(s2)
	lbu t2, 441(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 442(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 443(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 488(s4)
	xor t0, t0, t1
	sb t0, 440(s2)
	srli t2, t0, 8
	sb t2, 441(s2)
	srli t2, t0, 16
	sb t2, 442(s2)
	srli t2, t0, 24
	sb t2, 443(s2)
	lbu t0, 444(s2)
	lbu t2, 445(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 446(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 447(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 492(s4)
	xor t0, t0, t1
	sb t0, 444(s2)
	srli t2, t0, 8
	sb t2, 445(s2)
	srli t2, t0, 16
	sb t2, 446(s2)
	srli t2, t0, 24
	sb t2, 447(s2)
	lbu t0, 448(s2)
	lbu t2, 449(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 450(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 451(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 496(s4)
	xor t0, t0, t1
	sb t0, 448(s2)
	srli t2, t0, 8
	sb t2, 449(s2)
	srli t2, t0, 16
	sb t2, 450(s2)
	srli t2, t0, 24
	sb t2, 451(s2)
	lbu t0, 452(s2)
	lbu t2, 453(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 454(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 455(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 500(s4)
	xor t0, t0, t1
	sb t0, 452(s2)
	srli t2, t0, 8
	sb t2, 453(s2)
	srli t2, t0, 16
	sb t2, 454(s2)
	srli t2, t0, 24
	sb t2, 455(s2)
	lbu t0, 456(s2)
	lbu t2, 457(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 458(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 459(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 504(s4)
	xor t0, t0, t1
	sb t0, 456(s2)
	srli t2, t0, 8
	sb t2, 457(s2)
	srli t2, t0, 16
	sb t2, 458(s2)
	srli t2, t0, 24
	sb t2, 459(s2)
	lbu t0, 460(s2)
	lbu t2, 461(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 462(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 463(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 508(s4)
	xor t0, t0, t1
	sb t0, 460(s2)
	srli t2, t0, 8
	sb t2, 461(s2)
	srli t2, t0, 16
	sb t2, 462(s2)
	srli t2, t0, 24
	sb t2, 463(s2)
	lbu t0, 464(s2)
	lbu t2, 465(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 466(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 467(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 512(s4)
	xor t0, t0, t1
	sb t0, 464(s2)
	srli t2, t0, 8
	sb t2, 465(s2)
	srli t2, t0, 16
	sb t2, 466(s2)
	srli t2, t0, 24
	sb t2, 467(s2)
	lbu t0, 468(s2)
	lbu t2, 469(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 470(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 471(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 516(s4)
	xor t0, t0, t1
	sb t0, 468(s2)
	srli t2, t0, 8
	sb t2, 469(s2)
	srli t2, t0, 16
	sb t2, 470(s2)
	srli t2, t0, 24
	sb t2, 471(s2)
	lbu t0, 472(s2)
	lbu t2, 473(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 474(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 475(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 520(s4)
	xor t0, t0, t1
	sb t0, 472(s2)
	srli t2, t0, 8
	sb t2, 473(s2)
	srli t2, t0, 16
	sb t2, 474(s2)
	srli t2, t0, 24
	sb t2, 475(s2)
	lbu t0, 476(s2)
	lbu t2, 477(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 478(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 479(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 524(s4)
	xor t0, t0, t1
	sb t0, 476(s2)
	srli t2, t0, 8
	sb t2, 477(s2)
	srli t2, t0, 16
	sb t2, 478(s2)
	srli t2, t0, 24
	sb t2, 479(s2)
	lbu t0, 480(s2)
	lbu t2, 481(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 482(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 483(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 528(s4)
	xor t0, t0, t1
	sb t0, 480(s2)
	srli t2, t0, 8
	sb t2, 481(s2)
	srli t2, t0, 16
	sb t2, 482(s2)
	srli t2, t0, 24
	sb t2, 483(s2)
	lbu t0, 484(s2)
	lbu t2, 485(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 486(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 487(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 532(s4)
	xor t0, t0, t1
	sb t0, 484(s2)
	srli t2, t0, 8
	sb t2, 485(s2)
	srli t2, t0, 16
	sb t2, 486(s2)
	srli t2, t0, 24
	sb t2, 487(s2)
	lbu t0, 488(s2)
	lbu t2, 489(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 490(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 491(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 536(s4)
	xor t0, t0, t1
	sb t0, 488(s2)
	srli t2, t0, 8
	sb t2, 489(s2)
	srli t2, t0, 16
	sb t2, 490(s2)
	srli t2, t0, 24
	sb t2, 491(s2)
	lbu t0, 492(s2)
	lbu t2, 493(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 494(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 495(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 540(s4)
	xor t0, t0, t1
	sb t0, 492(s2)
	srli t2, t0, 8
	sb t2, 493(s2)
	srli t2, t0, 16
	sb t2, 494(s2)
	srli t2, t0, 24
	sb t2, 495(s2)
	lbu t0, 496(s2)
	lbu t2, 497(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 498(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 499(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 544(s4)
	xor t0, t0, t1
	sb t0, 496(s2)
	srli t2, t0, 8
	sb t2, 497(s2)
	srli t2, t0, 16
	sb t2, 498(s2)
	srli t2, t0, 24
	sb t2, 499(s2)
	lbu t0, 500(s2)
	lbu t2, 501(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 502(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 503(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 548(s4)
	xor t0, t0, t1
	sb t0, 500(s2)
	srli t2, t0, 8
	sb t2, 501(s2)
	srli t2, t0, 16
	sb t2, 502(s2)
	srli t2, t0, 24
	sb t2, 503(s2)
	lbu t0, 504(s2)
	lbu t2, 505(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 506(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 507(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 552(s4)
	xor t0, t0, t1
	sb t0, 504(s2)
	srli t2, t0, 8
	sb t2, 505(s2)
	srli t2, t0, 16
	sb t2, 506(s2)
	srli t2, t0, 24
	sb t2, 507(s2)
	lbu t0, 508(s2)
	lbu t2, 509(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 510(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 511(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 556(s4)
	xor t0, t0, t1
	sb t0, 508(s2)
	srli t2, t0, 8
	sb t2, 509(s2)
	srli t2, t0, 16
	sb t2, 510(s2)
	srli t2, t0, 24
	sb t2, 511(s2)
	addi s2, s2, 512
	addi s3, s3, -64
	srli t0, s3, 6
	bnez t0, 24b
	j 23f
22:
23:
	srli t0, s3, 5
	beqz t0, 25f
27:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 176(s4)
	lwu t0, 36(s4)
	sw t0, 180(s4)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 184(s4)
	lwu t0, 36(s4)
	sw t0, 188(s4)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 192(s4)
	lwu t0, 36(s4)
	sw t0, 196(s4)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 200(s4)
	lwu t0, 36(s4)
	sw t0, 204(s4)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 208(s4)
	lwu t0, 36(s4)
	sw t0, 212(s4)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 216(s4)
	lwu t0, 36(s4)
	sw t0, 220(s4)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 224(s4)
	lwu t0, 36(s4)
	sw t0, 228(s4)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 232(s4)
	lwu t0, 36(s4)
	sw t0, 236(s4)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 240(s4)
	lwu t0, 36(s4)
	sw t0, 244(s4)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 248(s4)
	lwu t0, 36(s4)
	sw t0, 252(s4)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 256(s4)
	lwu t0, 36(s4)
	sw t0, 260(s4)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 264(s4)
	lwu t0, 36(s4)
	sw t0, 268(s4)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 272(s4)
	lwu t0, 36(s4)
	sw t0, 276(s4)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 280(s4)
	lwu t0, 36(s4)
	sw t0, 284(s4)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 288(s4)
	lwu t0, 36(s4)
	sw t0, 292(s4)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 296(s4)
	lwu t0, 36(s4)
	sw t0, 300(s4)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 64(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 68(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 72(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 76(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 80(s4)
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 84(s4)
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 88(s4)
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 92(s4)
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 96(s4)
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 100(s4)
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 104(s4)
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 108(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 112(s4)
	xor t0, t0, t1
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 116(s4)
	xor t0, t0, t1
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 120(s4)
	xor t0, t0, t1
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 124(s4)
	xor t0, t0, t1
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 128(s4)
	xor t0, t0, t1
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 132(s4)
	xor t0, t0, t1
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 136(s4)
	xor t0, t0, t1
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 140(s4)
	xor t0, t0, t1
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 144(s4)
	xor t0, t0, t1
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 148(s4)
	xor t0, t0, t1
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 152(s4)
	xor t0, t0, t1
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 156(s4)
	xor t0, t0, t1
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 160(s4)
	xor t0, t0, t1
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 164(s4)
	xor t0, t0, t1
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 168(s4)
	xor t0, t0, t1
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 172(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 176(s4)
	xor t0, t0, t1
	sb t0, 128(s2)
	srli t2, t0, 8
	sb t2, 129(s2)
	srli t2, t0, 16
	sb t2, 130(s2)
	srli t2, t0, 24
	sb t2, 131(s2)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 180(s4)
	xor t0, t0, t1
	sb t0, 132(s2)
	srli t2, t0, 8
	sb t2, 133(s2)
	srli t2, t0, 16
	sb t2, 134(s2)
	srli t2, t0, 24
	sb t2, 135(s2)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 184(s4)
	xor t0, t0, t1
	sb t0, 136(s2)
	srli t2, t0, 8
	sb t2, 137(s2)
	srli t2, t0, 16
	sb t2, 138(s2)
	srli t2, t0, 24
	sb t2, 139(s2)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 188(s4)
	xor t0, t0, t1
	sb t0, 140(s2)
	srli t2, t0, 8
	sb t2, 141(s2)
	srli t2, t0, 16
	sb t2, 142(s2)
	srli t2, t0, 24
	sb t2, 143(s2)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 192(s4)
	xor t0, t0, t1
	sb t0, 144(s2)
	srli t2, t0, 8
	sb t2, 145(s2)
	srli t2, t0, 16
	sb t2, 146(s2)
	srli t2, t0, 24
	sb t2, 147(s2)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 196(s4)
	xor t0, t0, t1
	sb t0, 148(s2)
	srli t2, t0, 8
	sb t2, 149(s2)
	srli t2, t0, 16
	sb t2, 150(s2)
	srli t2, t0, 24
	sb t2, 151(s2)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 200(s4)
	xor t0, t0, t1
	sb t0, 152(s2)
	srli t2, t0, 8
	sb t2, 153(s2)
	srli t2, t0, 16
	sb t2, 154(s2)
	srli t2, t0, 24
	sb t2, 155(s2)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 204(s4)
	xor t0, t0, t1
	sb t0, 156(s2)
	srli t2, t0, 8
	sb t2, 157(s2)
	srli t2, t0, 16
	sb t2, 158(s2)
	srli t2, t0, 24
	sb t2, 159(s2)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 208(s4)
	xor t0, t0, t1
	sb t0, 160(s2)
	srli t2, t0, 8
	sb t2, 161(s2)
	srli t2, t0, 16
	sb t2, 162(s2)
	srli t2, t0, 24
	sb t2, 163(s2)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 212(s4)
	xor t0, t0, t1
	sb t0, 164(s2)
	srli t2, t0, 8
	sb t2, 165(s2)
	srli t2, t0, 16
	sb t2, 166(s2)
	srli t2, t0, 24
	sb t2, 167(s2)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 216(s4)
	xor t0, t0, t1
	sb t0, 168(s2)
	srli t2, t0, 8
	sb t2, 169(s2)
	srli t2, t0, 16
	sb t2, 170(s2)
	srli t2, t0, 24
	sb t2, 171(s2)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 220(s4)
	xor t0, t0, t1
	sb t0, 172(s2)
	srli t2, t0, 8
	sb t2, 173(s2)
	srli t2, t0, 16
	sb t2, 174(s2)
	srli t2, t0, 24
	sb t2, 175(s2)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 224(s4)
	xor t0, t0, t1
	sb t0, 176(s2)
	srli t2, t0, 8
	sb t2, 177(s2)
	srli t2, t0, 16
	sb t2, 178(s2)
	srli t2, t0, 24
	sb t2, 179(s2)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 228(s4)
	xor t0, t0, t1
	sb t0, 180(s2)
	srli t2, t0, 8
	sb t2, 181(s2)
	srli t2, t0, 16
	sb t2, 182(s2)
	srli t2, t0, 24
	sb t2, 183(s2)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 232(s4)
	xor t0, t0, t1
	sb t0, 184(s2)
	srli t2, t0, 8
	sb t2, 185(s2)
	srli t2, t0, 16
	sb t2, 186(s2)
	srli t2, t0, 24
	sb t2, 187(s2)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 236(s4)
	xor t0, t0, t1
	sb t0, 188(s2)
	srli t2, t0, 8
	sb t2, 189(s2)
	srli t2, t0, 16
	sb t2, 190(s2)
	srli t2, t0, 24
	sb t2, 191(s2)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 240(s4)
	xor t0, t0, t1
	sb t0, 192(s2)
	srli t2, t0, 8
	sb t2, 193(s2)
	srli t2, t0, 16
	sb t2, 194(s2)
	srli t2, t0, 24
	sb t2, 195(s2)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 244(s4)
	xor t0, t0, t1
	sb t0, 196(s2)
	srli t2, t0, 8
	sb t2, 197(s2)
	srli t2, t0, 16
	sb t2, 198(s2)
	srli t2, t0, 24
	sb t2, 199(s2)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 248(s4)
	xor t0, t0, t1
	sb t0, 200(s2)
	srli t2, t0, 8
	sb t2, 201(s2)
	srli t2, t0, 16
	sb t2, 202(s2)
	srli t2, t0, 24
	sb t2, 203(s2)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 252(s4)
	xor t0, t0, t1
	sb t0, 204(s2)
	srli t2, t0, 8
	sb t2, 205(s2)
	srli t2, t0, 16
	sb t2, 206(s2)
	srli t2, t0, 24
	sb t2, 207(s2)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 256(s4)
	xor t0, t0, t1
	sb t0, 208(s2)
	srli t2, t0, 8
	sb t2, 209(s2)
	srli t2, t0, 16
	sb t2, 210(s2)
	srli t2, t0, 24
	sb t2, 211(s2)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 260(s4)
	xor t0, t0, t1
	sb t0, 212(s2)
	srli t2, t0, 8
	sb t2, 213(s2)
	srli t2, t0, 16
	sb t2, 214(s2)
	srli t2, t0, 24
	sb t2, 215(s2)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 264(s4)
	xor t0, t0, t1
	sb t0, 216(s2)
	srli t2, t0, 8
	sb t2, 217(s2)
	srli t2, t0, 16
	sb t2, 218(s2)
	srli t2, t0, 24
	sb t2, 219(s2)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 268(s4)
	xor t0, t0, t1
	sb t0, 220(s2)
	srli t2, t0, 8
	sb t2, 221(s2)
	srli t2, t0, 16
	sb t2, 222(s2)
	srli t2, t0, 24
	sb t2, 223(s2)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 272(s4)
	xor t0, t0, t1
	sb t0, 224(s2)
	srli t2, t0, 8
	sb t2, 225(s2)
	srli t2, t0, 16
	sb t2, 226(s2)
	srli t2, t0, 24
	sb t2, 227(s2)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 276(s4)
	xor t0, t0, t1
	sb t0, 228(s2)
	srli t2, t0, 8
	sb t2, 229(s2)
	srli t2, t0, 16
	sb t2, 230(s2)
	srli t2, t0, 24
	sb t2, 231(s2)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 280(s4)
	xor t0, t0, t1
	sb t0, 232(s2)
	srli t2, t0, 8
	sb t2, 233(s2)
	srli t2, t0, 16
	sb t2, 234(s2)
	srli t2, t0, 24
	sb t2, 235(s2)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 284(s4)
	xor t0, t0, t1
	sb t0, 236(s2)
	srli t2, t0, 8
	sb t2, 237(s2)
	srli t2, t0, 16
	sb t2, 238(s2)
	srli t2, t0, 24
	sb t2, 239(s2)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 288(s4)
	xor t0, t0, t1
	sb t0, 240(s2)
	srli t2, t0, 8
	sb t2, 241(s2)
	srli t2, t0, 16
	sb t2, 242(s2)
	srli t2, t0, 24
	sb t2, 243(s2)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 292(s4)
	xor t0, t0, t1
	sb t0, 244(s2)
	srli t2, t0, 8
	sb t2, 245(s2)
	srli t2, t0, 16
	sb t2, 246(s2)
	srli t2, t0, 24
	sb t2, 247(s2)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 296(s4)
	xor t0, t0, t1
	sb t0, 248(s2)
	srli t2, t0, 8
	sb t2, 249(s2)
	srli t2, t0, 16
	sb t2, 250(s2)
	srli t2, t0, 24
	sb t2, 251(s2)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 300(s4)
	xor t0, t0, t1
	sb t0, 252(s2)
	srli t2, t0, 8
	sb t2, 253(s2)
	srli t2, t0, 16
	sb t2, 254(s2)
	srli t2, t0, 24
	sb t2, 255(s2)
	addi s2, s2, 256
	addi s3, s3, -32
	srli t0, s3, 5
	bnez t0, 27b
	j 26f
25:
26:
	srli t0, s3, 4
	beqz t0, 28f
210:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 64(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 68(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 72(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 76(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 80(s4)
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 84(s4)
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 88(s4)
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 92(s4)
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 96(s4)
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 100(s4)
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 104(s4)
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 108(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 112(s4)
	xor t0, t0, t1
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 116(s4)
	xor t0, t0, t1
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 120(s4)
	xor t0, t0, t1
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 124(s4)
	xor t0, t0, t1
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 128(s4)
	xor t0, t0, t1
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 132(s4)
	xor t0, t0, t1
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 136(s4)
	xor t0, t0, t1
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 140(s4)
	xor t0, t0, t1
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 144(s4)
	xor t0, t0, t1
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 148(s4)
	xor t0, t0, t1
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 152(s4)
	xor t0, t0, t1
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 156(s4)
	xor t0, t0, t1
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 160(s4)
	xor t0, t0, t1
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 164(s4)
	xor t0, t0, t1
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 168(s4)
	xor t0, t0, t1
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 172(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	addi s2, s2, 128
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 210b
	j 29f
28:
29:
	srli t0, s3, 3
	beqz t0, 211f
213:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 64(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 68(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 72(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 76(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 80(s4)
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 84(s4)
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 88(s4)
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 92(s4)
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 96(s4)
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 100(s4)
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 104(s4)
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 108(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	addi s2, s2, 64
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 213b
	j 212f
211:
212:
	srli t0, s3, 2
	beqz t0, 214f
216:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 56(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 60(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 64(s4)
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 68(s4)
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 72(s4)
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 76(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	addi s2, s2, 32
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 216b
	j 215f
214:
215:
	beqz s3, 217f
219:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
220:
	addi t6, a6, -3
	beqz t6, 221f
	addi t6, a6, -2
	beqz t6, 223f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 224f
223:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
224:
	j 222f
221:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
222:
225:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 225b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 220b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 219b
	j 218f
217:
218:
	j 21f
20:
	srli t0, s3, 6
	beqz t0, 226f
228:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lwu t0, 8(s2)
	sw t0, 32(s4)
	lwu t0, 12(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lwu t0, 24(s2)
	sw t0, 32(s4)
	lwu t0, 28(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lwu t0, 32(s2)
	sw t0, 32(s4)
	lwu t0, 36(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lwu t0, 40(s2)
	sw t0, 32(s4)
	lwu t0, 44(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lwu t0, 48(s2)
	sw t0, 32(s4)
	lwu t0, 52(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lwu t0, 56(s2)
	sw t0, 32(s4)
	lwu t0, 60(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lwu t0, 64(s2)
	sw t0, 32(s4)
	lwu t0, 68(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lwu t0, 72(s2)
	sw t0, 32(s4)
	lwu t0, 76(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lwu t0, 80(s2)
	sw t0, 32(s4)
	lwu t0, 84(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lwu t0, 88(s2)
	sw t0, 32(s4)
	lwu t0, 92(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lwu t0, 96(s2)
	sw t0, 32(s4)
	lwu t0, 100(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lwu t0, 104(s2)
	sw t0, 32(s4)
	lwu t0, 108(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lwu t0, 112(s2)
	sw t0, 32(s4)
	lwu t0, 116(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lwu t0, 120(s2)
	sw t0, 32(s4)
	lwu t0, 124(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 176(s4)
	lwu t0, 36(s4)
	sw t0, 180(s4)
	lwu t0, 128(s2)
	sw t0, 32(s4)
	lwu t0, 132(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 184(s4)
	lwu t0, 36(s4)
	sw t0, 188(s4)
	lwu t0, 136(s2)
	sw t0, 32(s4)
	lwu t0, 140(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 192(s4)
	lwu t0, 36(s4)
	sw t0, 196(s4)
	lwu t0, 144(s2)
	sw t0, 32(s4)
	lwu t0, 148(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 200(s4)
	lwu t0, 36(s4)
	sw t0, 204(s4)
	lwu t0, 152(s2)
	sw t0, 32(s4)
	lwu t0, 156(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 208(s4)
	lwu t0, 36(s4)
	sw t0, 212(s4)
	lwu t0, 160(s2)
	sw t0, 32(s4)
	lwu t0, 164(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 216(s4)
	lwu t0, 36(s4)
	sw t0, 220(s4)
	lwu t0, 168(s2)
	sw t0, 32(s4)
	lwu t0, 172(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 224(s4)
	lwu t0, 36(s4)
	sw t0, 228(s4)
	lwu t0, 176(s2)
	sw t0, 32(s4)
	lwu t0, 180(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 232(s4)
	lwu t0, 36(s4)
	sw t0, 236(s4)
	lwu t0, 184(s2)
	sw t0, 32(s4)
	lwu t0, 188(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 240(s4)
	lwu t0, 36(s4)
	sw t0, 244(s4)
	lwu t0, 192(s2)
	sw t0, 32(s4)
	lwu t0, 196(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 248(s4)
	lwu t0, 36(s4)
	sw t0, 252(s4)
	lwu t0, 200(s2)
	sw t0, 32(s4)
	lwu t0, 204(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 256(s4)
	lwu t0, 36(s4)
	sw t0, 260(s4)
	lwu t0, 208(s2)
	sw t0, 32(s4)
	lwu t0, 212(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 264(s4)
	lwu t0, 36(s4)
	sw t0, 268(s4)
	lwu t0, 216(s2)
	sw t0, 32(s4)
	lwu t0, 220(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 272(s4)
	lwu t0, 36(s4)
	sw t0, 276(s4)
	lwu t0, 224(s2)
	sw t0, 32(s4)
	lwu t0, 228(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 280(s4)
	lwu t0, 36(s4)
	sw t0, 284(s4)
	lwu t0, 232(s2)
	sw t0, 32(s4)
	lwu t0, 236(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 288(s4)
	lwu t0, 36(s4)
	sw t0, 292(s4)
	lwu t0, 240(s2)
	sw t0, 32(s4)
	lwu t0, 244(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 296(s4)
	lwu t0, 36(s4)
	sw t0, 300(s4)
	lwu t0, 248(s2)
	sw t0, 32(s4)
	lwu t0, 252(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 304(s4)
	lwu t0, 36(s4)
	sw t0, 308(s4)
	lwu t0, 256(s2)
	sw t0, 32(s4)
	lwu t0, 260(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 312(s4)
	lwu t0, 36(s4)
	sw t0, 316(s4)
	lwu t0, 264(s2)
	sw t0, 32(s4)
	lwu t0, 268(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 320(s4)
	lwu t0, 36(s4)
	sw t0, 324(s4)
	lwu t0, 272(s2)
	sw t0, 32(s4)
	lwu t0, 276(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 328(s4)
	lwu t0, 36(s4)
	sw t0, 332(s4)
	lwu t0, 280(s2)
	sw t0, 32(s4)
	lwu t0, 284(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 336(s4)
	lwu t0, 36(s4)
	sw t0, 340(s4)
	lwu t0, 288(s2)
	sw t0, 32(s4)
	lwu t0, 292(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 344(s4)
	lwu t0, 36(s4)
	sw t0, 348(s4)
	lwu t0, 296(s2)
	sw t0, 32(s4)
	lwu t0, 300(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 352(s4)
	lwu t0, 36(s4)
	sw t0, 356(s4)
	lwu t0, 304(s2)
	sw t0, 32(s4)
	lwu t0, 308(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 360(s4)
	lwu t0, 36(s4)
	sw t0, 364(s4)
	lwu t0, 312(s2)
	sw t0, 32(s4)
	lwu t0, 316(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 368(s4)
	lwu t0, 36(s4)
	sw t0, 372(s4)
	lwu t0, 320(s2)
	sw t0, 32(s4)
	lwu t0, 324(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 376(s4)
	lwu t0, 36(s4)
	sw t0, 380(s4)
	lwu t0, 328(s2)
	sw t0, 32(s4)
	lwu t0, 332(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 384(s4)
	lwu t0, 36(s4)
	sw t0, 388(s4)
	lwu t0, 336(s2)
	sw t0, 32(s4)
	lwu t0, 340(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 392(s4)
	lwu t0, 36(s4)
	sw t0, 396(s4)
	lwu t0, 344(s2)
	sw t0, 32(s4)
	lwu t0, 348(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 400(s4)
	lwu t0, 36(s4)
	sw t0, 404(s4)
	lwu t0, 352(s2)
	sw t0, 32(s4)
	lwu t0, 356(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 408(s4)
	lwu t0, 36(s4)
	sw t0, 412(s4)
	lwu t0, 360(s2)
	sw t0, 32(s4)
	lwu t0, 364(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 416(s4)
	lwu t0, 36(s4)
	sw t0, 420(s4)
	lwu t0, 368(s2)
	sw t0, 32(s4)
	lwu t0, 372(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 424(s4)
	lwu t0, 36(s4)
	sw t0, 428(s4)
	lwu t0, 376(s2)
	sw t0, 32(s4)
	lwu t0, 380(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 432(s4)
	lwu t0, 36(s4)
	sw t0, 436(s4)
	lwu t0, 384(s2)
	sw t0, 32(s4)
	lwu t0, 388(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 440(s4)
	lwu t0, 36(s4)
	sw t0, 444(s4)
	lwu t0, 392(s2)
	sw t0, 32(s4)
	lwu t0, 396(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 448(s4)
	lwu t0, 36(s4)
	sw t0, 452(s4)
	lwu t0, 400(s2)
	sw t0, 32(s4)
	lwu t0, 404(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 456(s4)
	lwu t0, 36(s4)
	sw t0, 460(s4)
	lwu t0, 408(s2)
	sw t0, 32(s4)
	lwu t0, 412(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 464(s4)
	lwu t0, 36(s4)
	sw t0, 468(s4)
	lwu t0, 416(s2)
	sw t0, 32(s4)
	lwu t0, 420(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 472(s4)
	lwu t0, 36(s4)
	sw t0, 476(s4)
	lwu t0, 424(s2)
	sw t0, 32(s4)
	lwu t0, 428(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 480(s4)
	lwu t0, 36(s4)
	sw t0, 484(s4)
	lwu t0, 432(s2)
	sw t0, 32(s4)
	lwu t0, 436(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 488(s4)
	lwu t0, 36(s4)
	sw t0, 492(s4)
	lwu t0, 440(s2)
	sw t0, 32(s4)
	lwu t0, 444(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 496(s4)
	lwu t0, 36(s4)
	sw t0, 500(s4)
	lwu t0, 448(s2)
	sw t0, 32(s4)
	lwu t0, 452(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 504(s4)
	lwu t0, 36(s4)
	sw t0, 508(s4)
	lwu t0, 456(s2)
	sw t0, 32(s4)
	lwu t0, 460(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 512(s4)
	lwu t0, 36(s4)
	sw t0, 516(s4)
	lwu t0, 464(s2)
	sw t0, 32(s4)
	lwu t0, 468(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 520(s4)
	lwu t0, 36(s4)
	sw t0, 524(s4)
	lwu t0, 472(s2)
	sw t0, 32(s4)
	lwu t0, 476(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 528(s4)
	lwu t0, 36(s4)
	sw t0, 532(s4)
	lwu t0, 480(s2)
	sw t0, 32(s4)
	lwu t0, 484(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 536(s4)
	lwu t0, 36(s4)
	sw t0, 540(s4)
	lwu t0, 488(s2)
	sw t0, 32(s4)
	lwu t0, 492(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 544(s4)
	lwu t0, 36(s4)
	sw t0, 548(s4)
	lwu t0, 496(s2)
	sw t0, 32(s4)
	lwu t0, 500(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 552(s4)
	lwu t0, 36(s4)
	sw t0, 556(s4)
	lwu t0, 504(s2)
	sw t0, 32(s4)
	lwu t0, 508(s2)
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 56(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 60(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 64(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 68(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 72(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 76(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 80(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 84(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 88(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 92(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 96(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 100(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 104(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 108(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 112(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 116(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 120(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 124(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 128(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 132(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 136(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 140(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 144(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 148(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 152(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 156(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 160(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 164(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 168(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 172(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	lwu t0, 128(s2)
	lwu t1, 176(s4)
	xor t0, t0, t1
	sw t0, 128(s2)
	lwu t0, 132(s2)
	lwu t1, 180(s4)
	xor t0, t0, t1
	sw t0, 132(s2)
	lwu t0, 136(s2)
	lwu t1, 184(s4)
	xor t0, t0, t1
	sw t0, 136(s2)
	lwu t0, 140(s2)
	lwu t1, 188(s4)
	xor t0, t0, t1
	sw t0, 140(s2)
	lwu t0, 144(s2)
	lwu t1, 192(s4)
	xor t0, t0, t1
	sw t0, 144(s2)
	lwu t0, 148(s2)
	lwu t1, 196(s4)
	xor t0, t0, t1
	sw t0, 148(s2)
	lwu t0, 152(s2)
	lwu t1, 200(s4)
	xor t0, t0, t1
	sw t0, 152(s2)
	lwu t0, 156(s2)
	lwu t1, 204(s4)
	xor t0, t0, t1
	sw t0, 156(s2)
	lwu t0, 160(s2)
	lwu t1, 208(s4)
	xor t0, t0, t1
	sw t0, 160(s2)
	lwu t0, 164(s2)
	lwu t1, 212(s4)
	xor t0, t0, t1
	sw t0, 164(s2)
	lwu t0, 168(s2)
	lwu t1, 216(s4)
	xor t0, t0, t1
	sw t0, 168(s2)
	lwu t0, 172(s2)
	lwu t1, 220(s4)
	xor t0, t0, t1
	sw t0, 172(s2)
	lwu t0, 176(s2)
	lwu t1, 224(s4)
	xor t0, t0, t1
	sw t0, 176(s2)
	lwu t0, 180(s2)
	lwu t1, 228(s4)
	xor t0, t0, t1
	sw t0, 180(s2)
	lwu t0, 184(s2)
	lwu t1, 232(s4)
	xor t0, t0, t1
	sw t0, 184(s2)
	lwu t0, 188(s2)
	lwu t1, 236(s4)
	xor t0, t0, t1
	sw t0, 188(s2)
	lwu t0, 192(s2)
	lwu t1, 240(s4)
	xor t0, t0, t1
	sw t0, 192(s2)
	lwu t0, 196(s2)
	lwu t1, 244(s4)
	xor t0, t0, t1
	sw t0, 196(s2)
	lwu t0, 200(s2)
	lwu t1, 248(s4)
	xor t0, t0, t1
	sw t0, 200(s2)
	lwu t0, 204(s2)
	lwu t1, 252(s4)
	xor t0, t0, t1
	sw t0, 204(s2)
	lwu t0, 208(s2)
	lwu t1, 256(s4)
	xor t0, t0, t1
	sw t0, 208(s2)
	lwu t0, 212(s2)
	lwu t1, 260(s4)
	xor t0, t0, t1
	sw t0, 212(s2)
	lwu t0, 216(s2)
	lwu t1, 264(s4)
	xor t0, t0, t1
	sw t0, 216(s2)
	lwu t0, 220(s2)
	lwu t1, 268(s4)
	xor t0, t0, t1
	sw t0, 220(s2)
	lwu t0, 224(s2)
	lwu t1, 272(s4)
	xor t0, t0, t1
	sw t0, 224(s2)
	lwu t0, 228(s2)
	lwu t1, 276(s4)
	xor t0, t0, t1
	sw t0, 228(s2)
	lwu t0, 232(s2)
	lwu t1, 280(s4)
	xor t0, t0, t1
	sw t0, 232(s2)
	lwu t0, 236(s2)
	lwu t1, 284(s4)
	xor t0, t0, t1
	sw t0, 236(s2)
	lwu t0, 240(s2)
	lwu t1, 288(s4)
	xor t0, t0, t1
	sw t0, 240(s2)
	lwu t0, 244(s2)
	lwu t1, 292(s4)
	xor t0, t0, t1
	sw t0, 244(s2)
	lwu t0, 248(s2)
	lwu t1, 296(s4)
	xor t0, t0, t1
	sw t0, 248(s2)
	lwu t0, 252(s2)
	lwu t1, 300(s4)
	xor t0, t0, t1
	sw t0, 252(s2)
	lwu t0, 256(s2)
	lwu t1, 304(s4)
	xor t0, t0, t1
	sw t0, 256(s2)
	lwu t0, 260(s2)
	lwu t1, 308(s4)
	xor t0, t0, t1
	sw t0, 260(s2)
	lwu t0, 264(s2)
	lwu t1, 312(s4)
	xor t0, t0, t1
	sw t0, 264(s2)
	lwu t0, 268(s2)
	lwu t1, 316(s4)
	xor t0, t0, t1
	sw t0, 268(s2)
	lwu t0, 272(s2)
	lwu t1, 320(s4)
	xor t0, t0, t1
	sw t0, 272(s2)
	lwu t0, 276(s2)
	lwu t1, 324(s4)
	xor t0, t0, t1
	sw t0, 276(s2)
	lwu t0, 280(s2)
	lwu t1, 328(s4)
	xor t0, t0, t1
	sw t0, 280(s2)
	lwu t0, 284(s2)
	lwu t1, 332(s4)
	xor t0, t0, t1
	sw t0, 284(s2)
	lwu t0, 288(s2)
	lwu t1, 336(s4)
	xor t0, t0, t1
	sw t0, 288(s2)
	lwu t0, 292(s2)
	lwu t1, 340(s4)
	xor t0, t0, t1
	sw t0, 292(s2)
	lwu t0, 296(s2)
	lwu t1, 344(s4)
	xor t0, t0, t1
	sw t0, 296(s2)
	lwu t0, 300(s2)
	lwu t1, 348(s4)
	xor t0, t0, t1
	sw t0, 300(s2)
	lwu t0, 304(s2)
	lwu t1, 352(s4)
	xor t0, t0, t1
	sw t0, 304(s2)
	lwu t0, 308(s2)
	lwu t1, 356(s4)
	xor t0, t0, t1
	sw t0, 308(s2)
	lwu t0, 312(s2)
	lwu t1, 360(s4)
	xor t0, t0, t1
	sw t0, 312(s2)
	lwu t0, 316(s2)
	lwu t1, 364(s4)
	xor t0, t0, t1
	sw t0, 316(s2)
	lwu t0, 320(s2)
	lwu t1, 368(s4)
	xor t0, t0, t1
	sw t0, 320(s2)
	lwu t0, 324(s2)
	lwu t1, 372(s4)
	xor t0, t0, t1
	sw t0, 324(s2)
	lwu t0, 328(s2)
	lwu t1, 376(s4)
	xor t0, t0, t1
	sw t0, 328(s2)
	lwu t0, 332(s2)
	lwu t1, 380(s4)
	xor t0, t0, t1
	sw t0, 332(s2)
	lwu t0, 336(s2)
	lwu t1, 384(s4)
	xor t0, t0, t1
	sw t0, 336(s2)
	lwu t0, 340(s2)
	lwu t1, 388(s4)
	xor t0, t0, t1
	sw t0, 340(s2)
	lwu t0, 344(s2)
	lwu t1, 392(s4)
	xor t0, t0, t1
	sw t0, 344(s2)
	lwu t0, 348(s2)
	lwu t1, 396(s4)
	xor t0, t0, t1
	sw t0, 348(s2)
	lwu t0, 352(s2)
	lwu t1, 400(s4)
	xor t0, t0, t1
	sw t0, 352(s2)
	lwu t0, 356(s2)
	lwu t1, 404(s4)
	xor t0, t0, t1
	sw t0, 356(s2)
	lwu t0, 360(s2)
	lwu t1, 408(s4)
	xor t0, t0, t1
	sw t0, 360(s2)
	lwu t0, 364(s2)
	lwu t1, 412(s4)
	xor t0, t0, t1
	sw t0, 364(s2)
	lwu t0, 368(s2)
	lwu t1, 416(s4)
	xor t0, t0, t1
	sw t0, 368(s2)
	lwu t0, 372(s2)
	lwu t1, 420(s4)
	xor t0, t0, t1
	sw t0, 372(s2)
	lwu t0, 376(s2)
	lwu t1, 424(s4)
	xor t0, t0, t1
	sw t0, 376(s2)
	lwu t0, 380(s2)
	lwu t1, 428(s4)
	xor t0, t0, t1
	sw t0, 380(s2)
	lwu t0, 384(s2)
	lwu t1, 432(s4)
	xor t0, t0, t1
	sw t0, 384(s2)
	lwu t0, 388(s2)
	lwu t1, 436(s4)
	xor t0, t0, t1
	sw t0, 388(s2)
	lwu t0, 392(s2)
	lwu t1, 440(s4)
	xor t0, t0, t1
	sw t0, 392(s2)
	lwu t0, 396(s2)
	lwu t1, 444(s4)
	xor t0, t0, t1
	sw t0, 396(s2)
	lwu t0, 400(s2)
	lwu t1, 448(s4)
	xor t0, t0, t1
	sw t0, 400(s2)
	lwu t0, 404(s2)
	lwu t1, 452(s4)
	xor t0, t0, t1
	sw t0, 404(s2)
	lwu t0, 408(s2)
	lwu t1, 456(s4)
	xor t0, t0, t1
	sw t0, 408(s2)
	lwu t0, 412(s2)
	lwu t1, 460(s4)
	xor t0, t0, t1
	sw t0, 412(s2)
	lwu t0, 416(s2)
	lwu t1, 464(s4)
	xor t0, t0, t1
	sw t0, 416(s2)
	lwu t0, 420(s2)
	lwu t1, 468(s4)
	xor t0, t0, t1
	sw t0, 420(s2)
	lwu t0, 424(s2)
	lwu t1, 472(s4)
	xor t0, t0, t1
	sw t0, 424(s2)
	lwu t0, 428(s2)
	lwu t1, 476(s4)
	xor t0, t0, t1
	sw t0, 428(s2)
	lwu t0, 432(s2)
	lwu t1, 480(s4)
	xor t0, t0, t1
	sw t0, 432(s2)
	lwu t0, 436(s2)
	lwu t1, 484(s4)
	xor t0, t0, t1
	sw t0, 436(s2)
	lwu t0, 440(s2)
	lwu t1, 488(s4)
	xor t0, t0, t1
	sw t0, 440(s2)
	lwu t0, 444(s2)
	lwu t1, 492(s4)
	xor t0, t0, t1
	sw t0, 444(s2)
	lwu t0, 448(s2)
	lwu t1, 496(s4)
	xor t0, t0, t1
	sw t0, 448(s2)
	lwu t0, 452(s2)
	lwu t1, 500(s4)
	xor t0, t0, t1
	sw t0, 452(s2)
	lwu t0, 456(s2)
	lwu t1, 504(s4)
	xor t0, t0, t1
	sw t0, 456(s2)
	lwu t0, 460(s2)
	lwu t1, 508(s4)
	xor t0, t0, t1
	sw t0, 460(s2)
	lwu t0, 464(s2)
	lwu t1, 512(s4)
	xor t0, t0, t1
	sw t0, 464(s2)
	lwu t0, 468(s2)
	lwu t1, 516(s4)
	xor t0, t0, t1
	sw t0, 468(s2)
	lwu t0, 472(s2)
	lwu t1, 520(s4)
	xor t0, t0, t1
	sw t0, 472(s2)
	lwu t0, 476(s2)
	lwu t1, 524(s4)
	xor t0, t0, t1
	sw t0, 476(s2)
	lwu t0, 480(s2)
	lwu t1, 528(s4)
	xor t0, t0, t1
	sw t0, 480(s2)
	lwu t0, 484(s2)
	lwu t1, 532(s4)
	xor t0, t0, t1
	sw t0, 484(s2)
	lwu t0, 488(s2)
	lwu t1, 536(s4)
	xor t0, t0, t1
	sw t0, 488(s2)
	lwu t0, 492(s2)
	lwu t1, 540(s4)
	xor t0, t0, t1
	sw t0, 492(s2)
	lwu t0, 496(s2)
	lwu t1, 544(s4)
	xor t0, t0, t1
	sw t0, 496(s2)
	lwu t0, 500(s2)
	lwu t1, 548(s4)
	xor t0, t0, t1
	sw t0, 500(s2)
	lwu t0, 504(s2)
	lwu t1, 552(s4)
	xor t0, t0, t1
	sw t0, 504(s2)
	lwu t0, 508(s2)
	lwu t1, 556(s4)
	xor t0, t0, t1
	sw t0, 508(s2)
	addi s2, s2, 512
	addi s3, s3, -64
	srli t0, s3, 6
	bnez t0, 228b
	j 227f
226:
227:
	srli t0, s3, 5
	beqz t0, 229f
231:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lwu t0, 8(s2)
	sw t0, 32(s4)
	lwu t0, 12(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lwu t0, 24(s2)
	sw t0, 32(s4)
	lwu t0, 28(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lwu t0, 32(s2)
	sw t0, 32(s4)
	lwu t0, 36(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lwu t0, 40(s2)
	sw t0, 32(s4)
	lwu t0, 44(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lwu t0, 48(s2)
	sw t0, 32(s4)
	lwu t0, 52(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lwu t0, 56(s2)
	sw t0, 32(s4)
	lwu t0, 60(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lwu t0, 64(s2)
	sw t0, 32(s4)
	lwu t0, 68(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lwu t0, 72(s2)
	sw t0, 32(s4)
	lwu t0, 76(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lwu t0, 80(s2)
	sw t0, 32(s4)
	lwu t0, 84(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lwu t0, 88(s2)
	sw t0, 32(s4)
	lwu t0, 92(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lwu t0, 96(s2)
	sw t0, 32(s4)
	lwu t0, 100(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lwu t0, 104(s2)
	sw t0, 32(s4)
	lwu t0, 108(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lwu t0, 112(s2)
	sw t0, 32(s4)
	lwu t0, 116(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lwu t0, 120(s2)
	sw t0, 32(s4)
	lwu t0, 124(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 176(s4)
	lwu t0, 36(s4)
	sw t0, 180(s4)
	lwu t0, 128(s2)
	sw t0, 32(s4)
	lwu t0, 132(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 184(s4)
	lwu t0, 36(s4)
	sw t0, 188(s4)
	lwu t0, 136(s2)
	sw t0, 32(s4)
	lwu t0, 140(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 192(s4)
	lwu t0, 36(s4)
	sw t0, 196(s4)
	lwu t0, 144(s2)
	sw t0, 32(s4)
	lwu t0, 148(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 200(s4)
	lwu t0, 36(s4)
	sw t0, 204(s4)
	lwu t0, 152(s2)
	sw t0, 32(s4)
	lwu t0, 156(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 208(s4)
	lwu t0, 36(s4)
	sw t0, 212(s4)
	lwu t0, 160(s2)
	sw t0, 32(s4)
	lwu t0, 164(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 216(s4)
	lwu t0, 36(s4)
	sw t0, 220(s4)
	lwu t0, 168(s2)
	sw t0, 32(s4)
	lwu t0, 172(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 224(s4)
	lwu t0, 36(s4)
	sw t0, 228(s4)
	lwu t0, 176(s2)
	sw t0, 32(s4)
	lwu t0, 180(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 232(s4)
	lwu t0, 36(s4)
	sw t0, 236(s4)
	lwu t0, 184(s2)
	sw t0, 32(s4)
	lwu t0, 188(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 240(s4)
	lwu t0, 36(s4)
	sw t0, 244(s4)
	lwu t0, 192(s2)
	sw t0, 32(s4)
	lwu t0, 196(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 248(s4)
	lwu t0, 36(s4)
	sw t0, 252(s4)
	lwu t0, 200(s2)
	sw t0, 32(s4)
	lwu t0, 204(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 256(s4)
	lwu t0, 36(s4)
	sw t0, 260(s4)
	lwu t0, 208(s2)
	sw t0, 32(s4)
	lwu t0, 212(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 264(s4)
	lwu t0, 36(s4)
	sw t0, 268(s4)
	lwu t0, 216(s2)
	sw t0, 32(s4)
	lwu t0, 220(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 272(s4)
	lwu t0, 36(s4)
	sw t0, 276(s4)
	lwu t0, 224(s2)
	sw t0, 32(s4)
	lwu t0, 228(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 280(s4)
	lwu t0, 36(s4)
	sw t0, 284(s4)
	lwu t0, 232(s2)
	sw t0, 32(s4)
	lwu t0, 236(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 288(s4)
	lwu t0, 36(s4)
	sw t0, 292(s4)
	lwu t0, 240(s2)
	sw t0, 32(s4)
	lwu t0, 244(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 296(s4)
	lwu t0, 36(s4)
	sw t0, 300(s4)
	lwu t0, 248(s2)
	sw t0, 32(s4)
	lwu t0, 252(s2)
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 56(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 60(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 64(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 68(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 72(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 76(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 80(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 84(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 88(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 92(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 96(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 100(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 104(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 108(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 112(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 116(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 120(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 124(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 128(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 132(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 136(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 140(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 144(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 148(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 152(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 156(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 160(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 164(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 168(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 172(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	lwu t0, 128(s2)
	lwu t1, 176(s4)
	xor t0, t0, t1
	sw t0, 128(s2)
	lwu t0, 132(s2)
	lwu t1, 180(s4)
	xor t0, t0, t1
	sw t0, 132(s2)
	lwu t0, 136(s2)
	lwu t1, 184(s4)
	xor t0, t0, t1
	sw t0, 136(s2)
	lwu t0, 140(s2)
	lwu t1, 188(s4)
	xor t0, t0, t1
	sw t0, 140(s2)
	lwu t0, 144(s2)
	lwu t1, 192(s4)
	xor t0, t0, t1
	sw t0, 144(s2)
	lwu t0, 148(s2)
	lwu t1, 196(s4)
	xor t0, t0, t1
	sw t0, 148(s2)
	lwu t0, 152(s2)
	lwu t1, 200(s4)
	xor t0, t0, t1
	sw t0, 152(s2)
	lwu t0, 156(s2)
	lwu t1, 204(s4)
	xor t0, t0, t1
	sw t0, 156(s2)
	lwu t0, 160(s2)
	lwu t1, 208(s4)
	xor t0, t0, t1
	sw t0, 160(s2)
	lwu t0, 164(s2)
	lwu t1, 212(s4)
	xor t0, t0, t1
	sw t0, 164(s2)
	lwu t0, 168(s2)
	lwu t1, 216(s4)
	xor t0, t0, t1
	sw t0, 168(s2)
	lwu t0, 172(s2)
	lwu t1, 220(s4)
	xor t0, t0, t1
	sw t0, 172(s2)
	lwu t0, 176(s2)
	lwu t1, 224(s4)
	xor t0, t0, t1
	sw t0, 176(s2)
	lwu t0, 180(s2)
	lwu t1, 228(s4)
	xor t0, t0, t1
	sw t0, 180(s2)
	lwu t0, 184(s2)
	lwu t1, 232(s4)
	xor t0, t0, t1
	sw t0, 184(s2)
	lwu t0, 188(s2)
	lwu t1, 236(s4)
	xor t0, t0, t1
	sw t0, 188(s2)
	lwu t0, 192(s2)
	lwu t1, 240(s4)
	xor t0, t0, t1
	sw t0, 192(s2)
	lwu t0, 196(s2)
	lwu t1, 244(s4)
	xor t0, t0, t1
	sw t0, 196(s2)
	lwu t0, 200(s2)
	lwu t1, 248(s4)
	xor t0, t0, t1
	sw t0, 200(s2)
	lwu t0, 204(s2)
	lwu t1, 252(s4)
	xor t0, t0, t1
	sw t0, 204(s2)
	lwu t0, 208(s2)
	lwu t1, 256(s4)
	xor t0, t0, t1
	sw t0, 208(s2)
	lwu t0, 212(s2)
	lwu t1, 260(s4)
	xor t0, t0, t1
	sw t0, 212(s2)
	lwu t0, 216(s2)
	lwu t1, 264(s4)
	xor t0, t0, t1
	sw t0, 216(s2)
	lwu t0, 220(s2)
	lwu t1, 268(s4)
	xor t0, t0, t1
	sw t0, 220(s2)
	lwu t0, 224(s2)
	lwu t1, 272(s4)
	xor t0, t0, t1
	sw t0, 224(s2)
	lwu t0, 228(s2)
	lwu t1, 276(s4)
	xor t0, t0, t1
	sw t0, 228(s2)
	lwu t0, 232(s2)
	lwu t1, 280(s4)
	xor t0, t0, t1
	sw t0, 232(s2)
	lwu t0, 236(s2)
	lwu t1, 284(s4)
	xor t0, t0, t1
	sw t0, 236(s2)
	lwu t0, 240(s2)
	lwu t1, 288(s4)
	xor t0, t0, t1
	sw t0, 240(s2)
	lwu t0, 244(s2)
	lwu t1, 292(s4)
	xor t0, t0, t1
	sw t0, 244(s2)
	lwu t0, 248(s2)
	lwu t1, 296(s4)
	xor t0, t0, t1
	sw t0, 248(s2)
	lwu t0, 252(s2)
	lwu t1, 300(s4)
	xor t0, t0, t1
	sw t0, 252(s2)
	addi s2, s2, 256
	addi s3, s3, -32
	srli t0, s3, 5
	bnez t0, 231b
	j 230f
229:
230:
	srli t0, s3, 4
	beqz t0, 232f
234:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lwu t0, 8(s2)
	sw t0, 32(s4)
	lwu t0, 12(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lwu t0, 24(s2)
	sw t0, 32(s4)
	lwu t0, 28(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lwu t0, 32(s2)
	sw t0, 32(s4)
	lwu t0, 36(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lwu t0, 40(s2)
	sw t0, 32(s4)
	lwu t0, 44(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lwu t0, 48(s2)
	sw t0, 32(s4)
	lwu t0, 52(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lwu t0, 56(s2)
	sw t0, 32(s4)
	lwu t0, 60(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 112(s4)
	lwu t0, 36(s4)
	sw t0, 116(s4)
	lwu t0, 64(s2)
	sw t0, 32(s4)
	lwu t0, 68(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 120(s4)
	lwu t0, 36(s4)
	sw t0, 124(s4)
	lwu t0, 72(s2)
	sw t0, 32(s4)
	lwu t0, 76(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 128(s4)
	lwu t0, 36(s4)
	sw t0, 132(s4)
	lwu t0, 80(s2)
	sw t0, 32(s4)
	lwu t0, 84(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 136(s4)
	lwu t0, 36(s4)
	sw t0, 140(s4)
	lwu t0, 88(s2)
	sw t0, 32(s4)
	lwu t0, 92(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 144(s4)
	lwu t0, 36(s4)
	sw t0, 148(s4)
	lwu t0, 96(s2)
	sw t0, 32(s4)
	lwu t0, 100(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 152(s4)
	lwu t0, 36(s4)
	sw t0, 156(s4)
	lwu t0, 104(s2)
	sw t0, 32(s4)
	lwu t0, 108(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 160(s4)
	lwu t0, 36(s4)
	sw t0, 164(s4)
	lwu t0, 112(s2)
	sw t0, 32(s4)
	lwu t0, 116(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 168(s4)
	lwu t0, 36(s4)
	sw t0, 172(s4)
	lwu t0, 120(s2)
	sw t0, 32(s4)
	lwu t0, 124(s2)
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 56(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 60(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 64(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 68(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 72(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 76(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 80(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 84(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 88(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 92(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 96(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 100(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 104(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 108(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 112(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 116(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 120(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 124(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 128(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 132(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 136(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 140(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 144(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 148(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 152(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 156(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 160(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 164(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 168(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 172(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	addi s2, s2, 128
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 234b
	j 233f
232:
233:
	srli t0, s3, 3
	beqz t0, 235f
237:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lwu t0, 8(s2)
	sw t0, 32(s4)
	lwu t0, 12(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lwu t0, 24(s2)
	sw t0, 32(s4)
	lwu t0, 28(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 80(s4)
	lwu t0, 36(s4)
	sw t0, 84(s4)
	lwu t0, 32(s2)
	sw t0, 32(s4)
	lwu t0, 36(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 88(s4)
	lwu t0, 36(s4)
	sw t0, 92(s4)
	lwu t0, 40(s2)
	sw t0, 32(s4)
	lwu t0, 44(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 96(s4)
	lwu t0, 36(s4)
	sw t0, 100(s4)
	lwu t0, 48(s2)
	sw t0, 32(s4)
	lwu t0, 52(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 104(s4)
	lwu t0, 36(s4)
	sw t0, 108(s4)
	lwu t0, 56(s2)
	sw t0, 32(s4)
	lwu t0, 60(s2)
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 56(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 60(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 64(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 68(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 72(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 76(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 80(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 84(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 88(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 92(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 96(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 100(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 104(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 108(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	addi s2, s2, 64
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 237b
	j 236f
235:
236:
	srli t0, s3, 2
	beqz t0, 238f
240:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 56(s4)
	lwu t0, 36(s4)
	sw t0, 60(s4)
	lwu t0, 8(s2)
	sw t0, 32(s4)
	lwu t0, 12(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 64(s4)
	lwu t0, 36(s4)
	sw t0, 68(s4)
	lwu t0, 16(s2)
	sw t0, 32(s4)
	lwu t0, 20(s2)
	sw t0, 36(s4)
	lwu t0, 32(s4)
	sw t0, 72(s4)
	lwu t0, 36(s4)
	sw t0, 76(s4)
	lwu t0, 24(s2)
	sw t0, 32(s4)
	lwu t0, 28(s2)
	sw t0, 36(s4)
	addi t6, s4, 2032
	addi t6, t6, -928
	sd ra, 0(t6)
	call {vg_triple_des_modes_crypt_encrypt}
	addi t6, s4, 2032
	addi t6, t6, -928
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 56(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 60(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 64(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 68(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 72(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 76(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	addi s2, s2, 32
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 240b
	j 239f
238:
239:
	beqz s3, 241f
243:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
244:
	addi t6, a6, -3
	beqz t6, 245f
	addi t6, a6, -2
	beqz t6, 247f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 248f
247:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
248:
	j 246f
245:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
246:
249:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 249b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 244b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 243b
	j 242f
241:
242:
21:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 140
250:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 250b
	addi sp, sp, 1120
	ret
	.option pop

vg_triple_des_cfb64_encrypt_final:
	.option push
	.option arch, +m, +c
	addi sp, sp, -944
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	addi t0, s4, 560
	addi t2, a0, 0
	addi t4, zero, 384
20:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 20b
	andi t0, s2, 3
	beqz t0, 21f
	beqz s3, 23f
25:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
26:
	addi t6, a6, -3
	beqz t6, 27f
	addi t6, a6, -2
	beqz t6, 29f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 210f
29:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
210:
	j 28f
27:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
28:
211:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 211b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 26b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi t0, zero, 8
	bltu s3, t0, 212f
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, s2, 8
	addi s3, s3, -8
	j 213f
212:
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	addi t2, s4, 48
214:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 214b
213:
	bnez s3, 25b
	j 24f
23:
24:
	j 22f
21:
	beqz s3, 215f
217:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
218:
	addi t6, a6, -3
	beqz t6, 219f
	addi t6, a6, -2
	beqz t6, 221f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 222f
221:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
222:
	j 220f
219:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
220:
223:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 223b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 218b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi t0, zero, 8
	bltu s3, t0, 224f
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	addi s2, s2, 8
	addi s3, s3, -8
	j 225f
224:
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	addi t2, s4, 48
226:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 226b
225:
	bnez s3, 217b
	j 216f
215:
216:
22:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 118
227:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 227b
	addi sp, sp, 944
	ret
	.option pop

vg_triple_des_cfb64_decrypt_final:
	.option push
	.option arch, +m, +c
	addi sp, sp, -944
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	addi s2, a2, 0
	addi t0, s4, 560
	addi t2, a0, 0
	addi t4, zero, 384
20:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 20b
	andi t0, s2, 3
	beqz t0, 21f
	beqz s3, 23f
25:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
26:
	addi t6, a6, -3
	beqz t6, 27f
	addi t6, a6, -2
	beqz t6, 29f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 210f
29:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
210:
	j 28f
27:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
28:
211:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 211b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 26b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi t0, zero, 8
	bltu s3, t0, 212f
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 48(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 52(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi s2, s2, 8
	addi s3, s3, -8
	j 213f
212:
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	addi t2, s4, 48
214:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 214b
213:
	bnez s3, 25b
	j 24f
23:
24:
	j 22f
21:
	beqz s3, 215f
217:
	lwu t0, 32(s4)
	sw t0, 48(s4)
	lwu t0, 36(s4)
	sw t0, 52(s4)
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 48(s4)
	slli t0, t0, 8
	lbu t1, 49(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 50(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 51(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 52(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 53(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 54(s4)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 55(s4)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
218:
	addi t6, a6, -3
	beqz t6, 219f
	addi t6, a6, -2
	beqz t6, 221f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 222f
221:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
222:
	j 220f
219:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
220:
223:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 223b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 218b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 48(s4)
	srli t1, t2, 48
	sb t1, 49(s4)
	srli t1, t2, 40
	sb t1, 50(s4)
	srli t1, t2, 32
	sb t1, 51(s4)
	srli t1, t2, 24
	sb t1, 52(s4)
	srli t1, t2, 16
	sb t1, 53(s4)
	srli t1, t2, 8
	sb t1, 54(s4)
	srli t1, t2, 0
	sb t1, 55(s4)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi t0, zero, 8
	bltu s3, t0, 224f
	lwu t0, 0(s2)
	sw t0, 32(s4)
	lwu t0, 4(s2)
	sw t0, 36(s4)
	lwu t0, 0(s2)
	lwu t1, 48(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 52(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	addi s2, s2, 8
	addi s3, s3, -8
	j 225f
224:
	lwu t0, 48(s4)
	sw t0, 32(s4)
	lwu t0, 52(s4)
	sw t0, 36(s4)
	addi t2, s4, 48
226:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 226b
225:
	bnez s3, 217b
	j 216f
215:
216:
22:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 118
227:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 227b
	addi sp, sp, 944
	ret
	.option pop
