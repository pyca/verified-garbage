// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
