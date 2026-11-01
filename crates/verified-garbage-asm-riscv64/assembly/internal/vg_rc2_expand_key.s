// The functions of `src/internal/vg_rc2_expand_key.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key:
	.option push
	.option arch, +m, +c
	lui t0, 973662
	addiw t0, t0, -742
	slli t0, t0, 32
	lui t1, 806808
	addiw t1, t1, -1831
	add t0, t0, t1
	sd t0, 0(a4)
	lui t0, 646538
	addiw t0, t0, 74
	slli t0, t0, 32
	lui t1, 499679
	addiw t1, t1, -1752
	add t0, t0, t1
	sd t0, 8(a4)
	lui t0, 582967
	addiw t0, t0, 1580
	slli t0, t0, 32
	lui t1, 537464
	addiw t1, t1, -314
	add t0, t0, t1
	sd t0, 16(a4)
	lui t0, 667577
	addiw t0, t0, -1211
	slli t0, t0, 32
	lui t1, 558661
	addiw t1, t1, -926
	add t0, t0, t1
	sd t0, 24(a4)
	lui t0, 79099
	addiw t0, t0, 904
	slli t0, t0, 32
	lui t1, 1004954
	addiw t1, t1, -1513
	add t0, t0, t1
	sd t0, 32(a4)
	lui t0, 206808
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 579284
	addiw t1, t1, 1377
	add t0, t0, t1
	sd t0, 40(a4)
	lui t0, 47035
	addiw t0, t0, 1927
	slli t0, t0, 32
	lui t1, 963593
	addiw t1, t1, -67
	add t0, t0, t1
	sd t0, 48(a4)
	lui t0, 533735
	addiw t0, t0, -1188
	slli t0, t0, 32
	lui t1, 139801
	addiw t1, t1, 1520
	add t0, t0, t1
	sd t0, 56(a4)
	lui t0, 117542
	addiw t0, t0, 207
	slli t0, t0, 32
	lui t1, 603741
	addiw t1, t1, 1620
	add t0, t0, t1
	sd t0, 64(a4)
	lui t0, 904985
	addiw t0, t0, -857
	slli t0, t0, 32
	lui t1, 84997
	addiw t1, t1, 1651
	add t0, t0, t1
	sd t0, 72(a4)
	lui t0, 859724
	addiw t0, t0, -453
	slli t0, t0, 32
	lui t1, 130215
	addiw t1, t1, 1298
	add t0, t0, t1
	sd t0, 80(a4)
	lui t0, 158564
	addiw t0, t0, -861
	slli t0, t0, 32
	lui t1, 200004
	addiw t1, t1, -702
	add t0, t0, t1
	sd t0, 88(a4)
	lui t0, 356471
	addiw t0, t0, -1721
	slli t0, t0, 32
	lui t1, 893164
	addiw t1, t1, -145
	add t0, t0, t1
	sd t0, 96(a4)
	lui t0, 13369
	addiw t0, t0, 1213
	slli t0, t0, 32
	lui t1, 635359
	addiw t1, t1, 551
	add t0, t0, t1
	sd t0, 104(a4)
	lui t0, 947183
	addiw t0, t0, -111
	slli t0, t0, 32
	lui t1, 1010801
	addiw t1, t1, 504
	add t0, t0, t1
	sd t0, 112(a4)
	lui t0, 881126
	addiw t0, t0, 1736
	slli t0, t0, 32
	lui t1, 195932
	addiw t1, t1, 774
	add t0, t0, t1
	sd t0, 120(a4)
	lui t0, 1015525
	addiw t0, t0, 641
	slli t0, t0, 32
	lui t1, 913071
	addiw t1, t1, -2040
	add t0, t0, t1
	sd t0, 128(a4)
	lui t0, 173733
	addiw t0, t0, -714
	slli t0, t0, 32
	lui t1, 706347
	addiw t1, t1, -1404
	add t0, t0, t1
	sd t0, 136(a4)
	lui t0, 476305
	addiw t0, t0, 1370
	slli t0, t0, 32
	lui t1, 466210
	addiw t1, t1, -1386
	add t0, t0, t1
	sd t0, 144(a4)
	lui t0, 969282
	addiw t0, t0, -2044
	slli t0, t0, 32
	lui t1, 388362
	addiw t1, t1, -181
	add t0, t0, t1
	sd t0, 152(a4)
	lui t0, 838837
	addiw t0, t0, 271
	slli t0, t0, 32
	lui t1, 451614
	addiw t1, t1, 194
	add t0, t0, t1
	sd t0, 160(a4)
	lui t0, 235279
	addiw t0, t0, 1185
	slli t0, t0, 32
	lui t1, 330489
	addiw t1, t1, 292
	add t0, t0, t1
	sd t0, 168(a4)
	lui t0, 502604
	addiw t0, t0, -2012
	slli t0, t0, 32
	lui t1, 545704
	addiw t1, t1, -871
	add t0, t0, t1
	sd t0, 176(a4)
	lui t0, 203125
	addiw t0, t0, 1317
	slli t0, t0, 32
	lui t1, 373600
	addiw t1, t1, 764
	add t0, t0, t1
	sd t0, 184(a4)
	lui t0, 715049
	addiw t0, t0, -1308
	slli t0, t0, 32
	lui t1, 626598
	addiw t1, t1, -723
	add t0, t0, t1
	sd t0, 192(a4)
	lui t0, 826279
	addiw t0, t0, -921
	slli t0, t0, 32
	lui t1, 66206
	addiw t1, t1, -251
	add t0, t0, t1
	sd t0, 200(a4)
	lui t0, 182922
	addiw t0, t0, -286
	slli t0, t0, 32
	lui t1, 851552
	addiw t1, t1, 211
	add t0, t0, t1
	sd t0, 208(a4)
	lui t0, 694430
	addiw t0, t0, 600
	slli t0, t0, 32
	lui t1, 258065
	addiw t1, t1, 1635
	add t0, t0, t1
	sd t0, 216(a4)
	lui t0, 724979
	addiw t0, t0, 939
	slli t0, t0, 32
	lui t1, 111428
	addiw t1, t1, -2035
	add t0, t0, t1
	sd t0, 224(a4)
	lui t0, 191707
	addiw t0, t0, 441
	slli t0, t0, 32
	lui t1, 389317
	addiw t1, t1, -1861
	add t0, t0, t1
	sd t0, 232(a4)
	lui t0, 489930
	addiw t0, t0, 1509
	slli t0, t0, 32
	lui t1, 294335
	addiw t1, t1, 965
	add t0, t0, t1
	sd t0, 240(a4)
	lui t0, 711704
	addiw t0, t0, -2
	slli t0, t0, 32
	lui t1, 426506
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(a4)
	addi a5, zero, 0
20:
	add a6, a0, a5
	lbu t2, 0(a6)
	add a6, a3, a5
	sb t2, 0(a6)
	addi a5, a5, 1
	sub a7, a5, a1
	bnez a7, 20b
	addi a7, zero, 128
	sub a7, a5, a7
	beqz a7, 21f
23:
	add a6, a3, a5
	addi a6, a6, -1
	lbu t0, 0(a6)
	sub a6, a5, a1
	add a6, a3, a6
	lbu t1, 0(a6)
	add t0, t0, t1
	slli t0, t0, 56
	srli t0, t0, 56
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	addi a5, a5, 1
	addi a7, zero, 128
	sub a7, a5, a7
	bnez a7, 23b
	j 22f
21:
22:
	addi t4, a2, 7
	srli t4, t4, 3
	addi a5, zero, 128
	sub a5, a5, t4
	slli a6, a2, 61
	srli a6, a6, 61
	addi t2, zero, 255
	addi t0, a6, -1
	beqz t0, 24f
	j 25f
24:
	addi t2, zero, 1
25:
	addi t0, a6, -2
	beqz t0, 26f
	j 27f
26:
	addi t2, zero, 3
27:
	addi t0, a6, -3
	beqz t0, 28f
	j 29f
28:
	addi t2, zero, 7
29:
	addi t0, a6, -4
	beqz t0, 210f
	j 211f
210:
	addi t2, zero, 15
211:
	addi t0, a6, -5
	beqz t0, 212f
	j 213f
212:
	addi t2, zero, 31
213:
	addi t0, a6, -6
	beqz t0, 214f
	j 215f
214:
	addi t2, zero, 63
215:
	addi t0, a6, -7
	beqz t0, 216f
	j 217f
216:
	addi t2, zero, 127
217:
	add a6, a3, a5
	lbu t0, 0(a6)
	and t0, t0, t2
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	beqz a5, 218f
220:
	addi a5, a5, -1
	add a6, a3, a5
	lbu t0, 1(a6)
	add a6, a5, t4
	add a6, a3, a6
	lbu t1, 0(a6)
	xor t0, t0, t1
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	bnez a5, 220b
	j 219f
218:
219:
	ret
	.option pop
