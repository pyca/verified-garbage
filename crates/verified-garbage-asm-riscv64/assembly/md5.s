// The functions of `src/md5.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
22:
	lbu t0, 0(a0)
	lbu t4, 1(a0)
	slli t4, t4, 8
	or t0, t0, t4
	lbu t4, 2(a0)
	slli t4, t4, 16
	or t0, t0, t4
	lbu t4, 3(a0)
	slli t4, t4, 24
	or t0, t0, t4
	lbu t1, 4(a0)
	lbu t4, 5(a0)
	slli t4, t4, 8
	or t1, t1, t4
	lbu t4, 6(a0)
	slli t4, t4, 16
	or t1, t1, t4
	lbu t4, 7(a0)
	slli t4, t4, 24
	or t1, t1, t4
	lbu t2, 8(a0)
	lbu t4, 9(a0)
	slli t4, t4, 8
	or t2, t2, t4
	lbu t4, 10(a0)
	slli t4, t4, 16
	or t2, t2, t4
	lbu t4, 11(a0)
	slli t4, t4, 24
	or t2, t2, t4
	lbu t3, 12(a0)
	lbu t4, 13(a0)
	slli t4, t4, 8
	or t3, t3, t4
	lbu t4, 14(a0)
	slli t4, t4, 16
	or t3, t3, t4
	lbu t4, 15(a0)
	slli t4, t4, 24
	or t3, t3, t4
	lbu t5, 0(a1)
	lbu t6, 1(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 2(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 3(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 882346
	addiw t5, t5, 1144
	add t0, t0, t5
	xor t4, t2, t3
	and t4, t4, t1
	xor t4, t4, t3
	add t0, t0, t4
	slliw t4, t0, 7
	srliw t0, t0, 25
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 4(a1)
	lbu t6, 5(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 6(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 7(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 953467
	addiw t5, t5, 1878
	add t3, t3, t5
	xor t4, t1, t2
	and t4, t4, t0
	xor t4, t4, t2
	add t3, t3, t4
	slliw t4, t3, 12
	srliw t3, t3, 20
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 8(a1)
	lbu t6, 9(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 10(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 11(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 147975
	addiw t5, t5, 219
	add t2, t2, t5
	xor t4, t0, t1
	and t4, t4, t3
	xor t4, t4, t1
	add t2, t2, t4
	slliw t4, t2, 17
	srliw t2, t2, 15
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 12(a1)
	lbu t6, 13(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 14(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 15(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 793565
	addiw t5, t5, -274
	add t1, t1, t5
	xor t4, t3, t0
	and t4, t4, t2
	xor t4, t4, t0
	add t1, t1, t4
	slliw t4, t1, 22
	srliw t1, t1, 10
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 16(a1)
	lbu t6, 17(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 18(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 19(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 1005505
	addiw t5, t5, -81
	add t0, t0, t5
	xor t4, t2, t3
	and t4, t4, t1
	xor t4, t4, t3
	add t0, t0, t4
	slliw t4, t0, 7
	srliw t0, t0, 25
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 20(a1)
	lbu t6, 21(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 22(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 23(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 292988
	addiw t5, t5, 1578
	add t3, t3, t5
	xor t4, t1, t2
	and t4, t4, t0
	xor t4, t4, t2
	add t3, t3, t4
	slliw t4, t3, 12
	srliw t3, t3, 20
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 24(a1)
	lbu t6, 25(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 26(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 27(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 688900
	addiw t5, t5, 1555
	add t2, t2, t5
	xor t4, t0, t1
	and t4, t4, t3
	xor t4, t4, t1
	add t2, t2, t4
	slliw t4, t2, 17
	srliw t2, t2, 15
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 28(a1)
	lbu t6, 29(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 30(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 31(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 1037417
	addiw t5, t5, 1281
	add t1, t1, t5
	xor t4, t3, t0
	and t4, t4, t2
	xor t4, t4, t0
	add t1, t1, t4
	slliw t4, t1, 22
	srliw t1, t1, 10
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 32(a1)
	lbu t6, 33(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 34(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 35(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 432138
	addiw t5, t5, -1832
	add t0, t0, t5
	xor t4, t2, t3
	and t4, t4, t1
	xor t4, t4, t3
	add t0, t0, t4
	slliw t4, t0, 7
	srliw t0, t0, 25
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 36(a1)
	lbu t6, 37(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 38(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 39(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 570447
	addiw t5, t5, 1967
	add t3, t3, t5
	xor t4, t1, t2
	and t4, t4, t0
	xor t4, t4, t2
	add t3, t3, t4
	slliw t4, t3, 12
	srliw t3, t3, 20
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 40(a1)
	lbu t6, 41(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 42(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 43(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 1048566
	addiw t5, t5, -1103
	add t2, t2, t5
	xor t4, t0, t1
	and t4, t4, t3
	xor t4, t4, t1
	add t2, t2, t4
	slliw t4, t2, 17
	srliw t2, t2, 15
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 44(a1)
	lbu t6, 45(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 46(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 47(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 562637
	addiw t5, t5, 1982
	add t1, t1, t5
	xor t4, t3, t0
	and t4, t4, t2
	xor t4, t4, t0
	add t1, t1, t4
	slliw t4, t1, 22
	srliw t1, t1, 10
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 48(a1)
	lbu t6, 49(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 50(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 51(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 440577
	addiw t5, t5, 290
	add t0, t0, t5
	xor t4, t2, t3
	and t4, t4, t1
	xor t4, t4, t3
	add t0, t0, t4
	slliw t4, t0, 7
	srliw t0, t0, 25
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 52(a1)
	lbu t6, 53(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 54(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 55(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 1038727
	addiw t5, t5, 403
	add t3, t3, t5
	xor t4, t1, t2
	and t4, t4, t0
	xor t4, t4, t2
	add t3, t3, t4
	slliw t4, t3, 12
	srliw t3, t3, 20
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 56(a1)
	lbu t6, 57(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 58(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 59(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 681876
	addiw t5, t5, 910
	add t2, t2, t5
	xor t4, t0, t1
	and t4, t4, t3
	xor t4, t4, t1
	add t2, t2, t4
	slliw t4, t2, 17
	srliw t2, t2, 15
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 60(a1)
	lbu t6, 61(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 62(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 63(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 301889
	addiw t5, t5, -2015
	add t1, t1, t5
	xor t4, t3, t0
	and t4, t4, t2
	xor t4, t4, t0
	add t1, t1, t4
	slliw t4, t1, 22
	srliw t1, t1, 10
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 4(a1)
	lbu t6, 5(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 6(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 7(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 1008098
	addiw t5, t5, 1378
	add t0, t0, t5
	xori t4, t3, -1
	and t4, t4, t2
	add t0, t0, t4
	and t4, t3, t1
	add t0, t0, t4
	slliw t4, t0, 5
	srliw t0, t0, 27
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 24(a1)
	lbu t6, 25(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 26(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 27(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 787467
	addiw t5, t5, 832
	add t3, t3, t5
	xori t4, t2, -1
	and t4, t4, t1
	add t3, t3, t4
	and t4, t2, t0
	add t3, t3, t4
	slliw t4, t3, 9
	srliw t3, t3, 23
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 44(a1)
	lbu t6, 45(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 46(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 47(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 157158
	addiw t5, t5, -1455
	add t2, t2, t5
	xori t4, t1, -1
	and t4, t4, t0
	add t2, t2, t4
	and t4, t1, t3
	add t2, t2, t4
	slliw t4, t2, 14
	srliw t2, t2, 18
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 0(a1)
	lbu t6, 1(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 2(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 3(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 957292
	addiw t5, t5, 1962
	add t1, t1, t5
	xori t4, t0, -1
	and t4, t4, t3
	add t1, t1, t4
	and t4, t0, t2
	add t1, t1, t4
	slliw t4, t1, 20
	srliw t1, t1, 12
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 20(a1)
	lbu t6, 21(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 22(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 23(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 877297
	addiw t5, t5, 93
	add t0, t0, t5
	xori t4, t3, -1
	and t4, t4, t2
	add t0, t0, t4
	and t4, t3, t1
	add t0, t0, t4
	slliw t4, t0, 5
	srliw t0, t0, 27
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 40(a1)
	lbu t6, 41(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 42(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 43(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 9281
	addiw t5, t5, 1107
	add t3, t3, t5
	xori t4, t2, -1
	and t4, t4, t1
	add t3, t3, t4
	and t4, t2, t0
	add t3, t3, t4
	slliw t4, t3, 9
	srliw t3, t3, 23
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 60(a1)
	lbu t6, 61(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 62(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 63(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 887326
	addiw t5, t5, 1665
	add t2, t2, t5
	xori t4, t1, -1
	and t4, t4, t0
	add t2, t2, t4
	and t4, t1, t3
	add t2, t2, t4
	slliw t4, t2, 14
	srliw t2, t2, 18
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 16(a1)
	lbu t6, 17(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 18(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 19(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 949568
	addiw t5, t5, -1080
	add t1, t1, t5
	xori t4, t0, -1
	and t4, t4, t3
	add t1, t1, t4
	and t4, t0, t2
	add t1, t1, t4
	slliw t4, t1, 20
	srliw t1, t1, 12
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 36(a1)
	lbu t6, 37(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 38(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 39(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 138781
	addiw t5, t5, -538
	add t0, t0, t5
	xori t4, t3, -1
	and t4, t4, t2
	add t0, t0, t4
	and t4, t3, t1
	add t0, t0, t4
	slliw t4, t0, 5
	srliw t0, t0, 27
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 56(a1)
	lbu t6, 57(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 58(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 59(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 799600
	addiw t5, t5, 2006
	add t3, t3, t5
	xori t4, t2, -1
	and t4, t4, t1
	add t3, t3, t4
	and t4, t2, t0
	add t3, t3, t4
	slliw t4, t3, 9
	srliw t3, t3, 23
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 12(a1)
	lbu t6, 13(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 14(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 15(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 1002833
	addiw t5, t5, -633
	add t2, t2, t5
	xori t4, t1, -1
	and t4, t4, t0
	add t2, t2, t4
	and t4, t1, t3
	add t2, t2, t4
	slliw t4, t2, 14
	srliw t2, t2, 18
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 32(a1)
	lbu t6, 33(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 34(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 35(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 284065
	addiw t5, t5, 1261
	add t1, t1, t5
	xori t4, t0, -1
	and t4, t4, t3
	add t1, t1, t4
	and t4, t0, t2
	add t1, t1, t4
	slliw t4, t1, 20
	srliw t1, t1, 12
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 52(a1)
	lbu t6, 53(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 54(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 55(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 695871
	addiw t5, t5, -1787
	add t0, t0, t5
	xori t4, t3, -1
	and t4, t4, t2
	add t0, t0, t4
	and t4, t3, t1
	add t0, t0, t4
	slliw t4, t0, 5
	srliw t0, t0, 27
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 8(a1)
	lbu t6, 9(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 10(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 11(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 1036026
	addiw t5, t5, 1016
	add t3, t3, t5
	xori t4, t2, -1
	and t4, t4, t1
	add t3, t3, t4
	and t4, t2, t0
	add t3, t3, t4
	slliw t4, t3, 9
	srliw t3, t3, 23
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 28(a1)
	lbu t6, 29(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 30(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 31(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 423664
	addiw t5, t5, 729
	add t2, t2, t5
	xori t4, t1, -1
	and t4, t4, t0
	add t2, t2, t4
	and t4, t1, t3
	add t2, t2, t4
	slliw t4, t2, 14
	srliw t2, t2, 18
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 48(a1)
	lbu t6, 49(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 50(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 51(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 578213
	addiw t5, t5, -886
	add t1, t1, t5
	xori t4, t0, -1
	and t4, t4, t3
	add t1, t1, t4
	and t4, t0, t2
	add t1, t1, t4
	slliw t4, t1, 20
	srliw t1, t1, 12
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 20(a1)
	lbu t6, 21(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 22(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 23(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 1048484
	addiw t5, t5, -1726
	add t0, t0, t5
	xor t4, t2, t3
	xor t4, t4, t1
	add t0, t0, t4
	slliw t4, t0, 4
	srliw t0, t0, 28
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 32(a1)
	lbu t6, 33(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 34(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 35(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 554783
	addiw t5, t5, 1665
	add t3, t3, t5
	xor t4, t1, t2
	xor t4, t4, t0
	add t3, t3, t4
	slliw t4, t3, 11
	srliw t3, t3, 21
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 44(a1)
	lbu t6, 45(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 46(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 47(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 448982
	addiw t5, t5, 290
	add t2, t2, t5
	xor t4, t0, t1
	xor t4, t4, t3
	add t2, t2, t4
	slliw t4, t2, 16
	srliw t2, t2, 16
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 56(a1)
	lbu t6, 57(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 58(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 59(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 1039956
	addiw t5, t5, -2036
	add t1, t1, t5
	xor t4, t3, t0
	xor t4, t4, t2
	add t1, t1, t4
	slliw t4, t1, 23
	srliw t1, t1, 9
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 4(a1)
	lbu t6, 5(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 6(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 7(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 674799
	addiw t5, t5, -1468
	add t0, t0, t5
	xor t4, t2, t3
	xor t4, t4, t1
	add t0, t0, t4
	slliw t4, t0, 4
	srliw t0, t0, 28
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 16(a1)
	lbu t6, 17(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 18(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 19(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 310765
	addiw t5, t5, -87
	add t3, t3, t5
	xor t4, t1, t2
	xor t4, t4, t0
	add t3, t3, t4
	slliw t4, t3, 11
	srliw t3, t3, 21
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 28(a1)
	lbu t6, 29(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 30(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 31(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 1010613
	addiw t5, t5, -1184
	add t2, t2, t5
	xor t4, t0, t1
	xor t4, t4, t3
	add t2, t2, t4
	slliw t4, t2, 16
	srliw t2, t2, 16
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 40(a1)
	lbu t6, 41(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 42(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 43(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 781308
	addiw t5, t5, -912
	add t1, t1, t5
	xor t4, t3, t0
	xor t4, t4, t2
	add t1, t1, t4
	slliw t4, t1, 23
	srliw t1, t1, 9
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 52(a1)
	lbu t6, 53(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 54(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 55(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 166328
	addiw t5, t5, -314
	add t0, t0, t5
	xor t4, t2, t3
	xor t4, t4, t1
	add t0, t0, t4
	slliw t4, t0, 4
	srliw t0, t0, 28
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 0(a1)
	lbu t6, 1(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 2(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 3(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 961042
	addiw t5, t5, 2042
	add t3, t3, t5
	xor t4, t1, t2
	xor t4, t4, t0
	add t3, t3, t4
	slliw t4, t3, 11
	srliw t3, t3, 21
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 12(a1)
	lbu t6, 13(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 14(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 15(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 872179
	addiw t5, t5, 133
	add t2, t2, t5
	xor t4, t0, t1
	xor t4, t4, t3
	add t2, t2, t4
	slliw t4, t2, 16
	srliw t2, t2, 16
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 24(a1)
	lbu t6, 25(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 26(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 27(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 18562
	addiw t5, t5, -763
	add t1, t1, t5
	xor t4, t3, t0
	xor t4, t4, t2
	add t1, t1, t4
	slliw t4, t1, 23
	srliw t1, t1, 9
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 36(a1)
	lbu t6, 37(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 38(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 39(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 892237
	addiw t5, t5, 57
	add t0, t0, t5
	xor t4, t2, t3
	xor t4, t4, t1
	add t0, t0, t4
	slliw t4, t0, 4
	srliw t0, t0, 28
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 48(a1)
	lbu t6, 49(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 50(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 51(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 945594
	addiw t5, t5, -1563
	add t3, t3, t5
	xor t4, t1, t2
	xor t4, t4, t0
	add t3, t3, t4
	slliw t4, t3, 11
	srliw t3, t3, 21
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 60(a1)
	lbu t6, 61(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 62(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 63(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 129576
	addiw t5, t5, -776
	add t2, t2, t5
	xor t4, t0, t1
	xor t4, t4, t3
	add t2, t2, t4
	slliw t4, t2, 16
	srliw t2, t2, 16
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 8(a1)
	lbu t6, 9(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 10(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 11(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 805573
	addiw t5, t5, 1637
	add t1, t1, t5
	xor t4, t3, t0
	xor t4, t4, t2
	add t1, t1, t4
	slliw t4, t1, 23
	srliw t1, t1, 9
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 0(a1)
	lbu t6, 1(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 2(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 3(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 1000082
	addiw t5, t5, 580
	add t0, t0, t5
	xori t4, t3, -1
	or t4, t4, t1
	xor t4, t4, t2
	add t0, t0, t4
	slliw t4, t0, 6
	srliw t0, t0, 26
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 28(a1)
	lbu t6, 29(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 30(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 31(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 275120
	addiw t5, t5, -105
	add t3, t3, t5
	xori t4, t2, -1
	or t4, t4, t0
	xor t4, t4, t1
	add t3, t3, t4
	slliw t4, t3, 10
	srliw t3, t3, 22
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 56(a1)
	lbu t6, 57(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 58(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 59(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 702786
	addiw t5, t5, 935
	add t2, t2, t5
	xori t4, t1, -1
	or t4, t4, t3
	xor t4, t4, t0
	add t2, t2, t4
	slliw t4, t2, 15
	srliw t2, t2, 17
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 20(a1)
	lbu t6, 21(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 22(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 23(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 1034554
	addiw t5, t5, 57
	add t1, t1, t5
	xori t4, t0, -1
	or t4, t4, t2
	xor t4, t4, t3
	add t1, t1, t4
	slliw t4, t1, 21
	srliw t1, t1, 11
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 48(a1)
	lbu t6, 49(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 50(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 51(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 415158
	addiw t5, t5, -1597
	add t0, t0, t5
	xori t4, t3, -1
	or t4, t4, t1
	xor t4, t4, t2
	add t0, t0, t4
	slliw t4, t0, 6
	srliw t0, t0, 26
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 12(a1)
	lbu t6, 13(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 14(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 15(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 585933
	addiw t5, t5, -878
	add t3, t3, t5
	xori t4, t2, -1
	or t4, t4, t0
	xor t4, t4, t1
	add t3, t3, t4
	slliw t4, t3, 10
	srliw t3, t3, 22
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 40(a1)
	lbu t6, 41(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 42(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 43(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 1048319
	addiw t5, t5, 1149
	add t2, t2, t5
	xori t4, t1, -1
	or t4, t4, t3
	xor t4, t4, t0
	add t2, t2, t4
	slliw t4, t2, 15
	srliw t2, t2, 17
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 4(a1)
	lbu t6, 5(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 6(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 7(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 546886
	addiw t5, t5, -559
	add t1, t1, t5
	xori t4, t0, -1
	or t4, t4, t2
	xor t4, t4, t3
	add t1, t1, t4
	slliw t4, t1, 21
	srliw t1, t1, 11
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 32(a1)
	lbu t6, 33(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 34(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 35(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 457352
	addiw t5, t5, -433
	add t0, t0, t5
	xori t4, t3, -1
	or t4, t4, t1
	xor t4, t4, t2
	add t0, t0, t4
	slliw t4, t0, 6
	srliw t0, t0, 26
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 60(a1)
	lbu t6, 61(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 62(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 63(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 1041102
	addiw t5, t5, 1760
	add t3, t3, t5
	xori t4, t2, -1
	or t4, t4, t0
	xor t4, t4, t1
	add t3, t3, t4
	slliw t4, t3, 10
	srliw t3, t3, 22
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 24(a1)
	lbu t6, 25(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 26(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 27(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 667668
	addiw t5, t5, 788
	add t2, t2, t5
	xori t4, t1, -1
	or t4, t4, t3
	xor t4, t4, t0
	add t2, t2, t4
	slliw t4, t2, 15
	srliw t2, t2, 17
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 52(a1)
	lbu t6, 53(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 54(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 55(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 319617
	addiw t5, t5, 417
	add t1, t1, t5
	xori t4, t0, -1
	or t4, t4, t2
	xor t4, t4, t3
	add t1, t1, t4
	slliw t4, t1, 21
	srliw t1, t1, 11
	or t1, t1, t4
	add t1, t1, t2
	lbu t5, 16(a1)
	lbu t6, 17(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 18(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 19(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t0, t0, t5
	lui t5, 1013048
	addiw t5, t5, -382
	add t0, t0, t5
	xori t4, t3, -1
	or t4, t4, t1
	xor t4, t4, t2
	add t0, t0, t4
	slliw t4, t0, 6
	srliw t0, t0, 26
	or t0, t0, t4
	add t0, t0, t1
	lbu t5, 44(a1)
	lbu t6, 45(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 46(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 47(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t3, t3, t5
	lui t5, 775087
	addiw t5, t5, 565
	add t3, t3, t5
	xori t4, t2, -1
	or t4, t4, t0
	xor t4, t4, t1
	add t3, t3, t4
	slliw t4, t3, 10
	srliw t3, t3, 22
	or t3, t3, t4
	add t3, t3, t0
	lbu t5, 8(a1)
	lbu t6, 9(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 10(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 11(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t2, t2, t5
	lui t5, 175485
	addiw t5, t5, 699
	add t2, t2, t5
	xori t4, t1, -1
	or t4, t4, t3
	xor t4, t4, t0
	add t2, t2, t4
	slliw t4, t2, 15
	srliw t2, t2, 17
	or t2, t2, t4
	add t2, t2, t3
	lbu t5, 36(a1)
	lbu t6, 37(a1)
	slli t6, t6, 8
	or t5, t5, t6
	lbu t6, 38(a1)
	slli t6, t6, 16
	or t5, t5, t6
	lbu t6, 39(a1)
	slli t6, t6, 24
	or t5, t5, t6
	add t1, t1, t5
	lui t5, 964717
	addiw t5, t5, 913
	add t1, t1, t5
	xori t4, t0, -1
	or t4, t4, t2
	xor t4, t4, t3
	add t1, t1, t4
	slliw t4, t1, 21
	srliw t1, t1, 11
	or t1, t1, t4
	add t1, t1, t2
	lbu t4, 0(a0)
	lbu t5, 1(a0)
	slli t5, t5, 8
	or t4, t4, t5
	lbu t5, 2(a0)
	slli t5, t5, 16
	or t4, t4, t5
	lbu t5, 3(a0)
	slli t5, t5, 24
	or t4, t4, t5
	add t0, t0, t4
	sb t0, 0(a0)
	srli t4, t0, 8
	sb t4, 1(a0)
	srli t4, t0, 16
	sb t4, 2(a0)
	srli t4, t0, 24
	sb t4, 3(a0)
	lbu t4, 4(a0)
	lbu t5, 5(a0)
	slli t5, t5, 8
	or t4, t4, t5
	lbu t5, 6(a0)
	slli t5, t5, 16
	or t4, t4, t5
	lbu t5, 7(a0)
	slli t5, t5, 24
	or t4, t4, t5
	add t1, t1, t4
	sb t1, 4(a0)
	srli t4, t1, 8
	sb t4, 5(a0)
	srli t4, t1, 16
	sb t4, 6(a0)
	srli t4, t1, 24
	sb t4, 7(a0)
	lbu t4, 8(a0)
	lbu t5, 9(a0)
	slli t5, t5, 8
	or t4, t4, t5
	lbu t5, 10(a0)
	slli t5, t5, 16
	or t4, t4, t5
	lbu t5, 11(a0)
	slli t5, t5, 24
	or t4, t4, t5
	add t2, t2, t4
	sb t2, 8(a0)
	srli t4, t2, 8
	sb t4, 9(a0)
	srli t4, t2, 16
	sb t4, 10(a0)
	srli t4, t2, 24
	sb t4, 11(a0)
	lbu t4, 12(a0)
	lbu t5, 13(a0)
	slli t5, t5, 8
	or t4, t4, t5
	lbu t5, 14(a0)
	slli t5, t5, 16
	or t4, t4, t5
	lbu t5, 15(a0)
	slli t5, t5, 24
	or t4, t4, t5
	add t3, t3, t4
	sb t3, 12(a0)
	srli t4, t3, 8
	sb t4, 13(a0)
	srli t4, t3, 16
	sb t4, 14(a0)
	srli t4, t3, 24
	sb t4, 15(a0)
	addi a1, a1, 64
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ret
	.option pop

vg_md5_init:
	.option push
	.option arch, +m, +c
	lui t0, 422994
	addiw t0, t0, 769
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 982235
	addiw t0, t0, -1143
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 625582
	addiw t0, t0, -770
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 66341
	addiw t0, t0, 1142
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	ret
	.option pop

vg_md5_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 63
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 16(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -64
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 16
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 6
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 64
	addi s4, s4, -64
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 64
	sub t2, t2, s5
	srli t1, s4, 6
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 6
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 16(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -64
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 16
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop

vg_md5_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 80(t0)
	sd s1, 88(t0)
	sd s2, 96(t0)
	sd s3, 104(t0)
	sd s4, 112(t0)
	sd s5, 120(t0)
	sd s6, 128(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 63
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 16(t3)
	addi s5, s5, 1
	addi s6, s5, 7
	srli s6, s6, 6
20:
	addi t2, zero, 64
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 56
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 16(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	slli t1, s4, 3
	sb t1, 72(s1)
	srli t3, t1, 8
	sb t3, 73(s1)
	srli t3, t1, 16
	sb t3, 74(s1)
	srli t3, t1, 24
	sb t3, 75(s1)
	srli t1, t1, 32
	sb t1, 76(s1)
	srli t3, t1, 8
	sb t3, 77(s1)
	srli t3, t1, 16
	sb t3, 78(s1)
	srli t3, t1, 24
	sb t3, 79(s1)
27:
	addi a1, s1, 16
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_md5_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 0(s3)
	srli t2, t1, 8
	sb t2, 1(s3)
	srli t2, t1, 16
	sb t2, 2(s3)
	srli t2, t1, 24
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 4(s3)
	srli t2, t1, 8
	sb t2, 5(s3)
	srli t2, t1, 16
	sb t2, 6(s3)
	srli t2, t1, 24
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 8(s3)
	srli t2, t1, 8
	sb t2, 9(s3)
	srli t2, t1, 16
	sb t2, 10(s3)
	srli t2, t1, 24
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	sb t1, 12(s3)
	srli t2, t1, 8
	sb t2, 13(s3)
	srli t2, t1, 16
	sb t2, 14(s3)
	srli t2, t1, 24
	sb t2, 15(s3)
	ld ra, 80(s2)
	ld s1, 88(s2)
	ld s3, 104(s2)
	ld s4, 112(s2)
	ld s5, 120(s2)
	ld s6, 128(s2)
	ld s2, 96(s2)
	addi sp, sp, 144
	ret
	.option pop
