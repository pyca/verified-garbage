// The functions of `src/ec_p192_compressed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_compress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	addi t0, zero, 0
	sd t0, 1144(s0)
	lbu t0, 1(a1)
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 9(a1)
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 17(a1)
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	sd t0, 1120(s0)
	addi t0, zero, 0
	sd t0, 1240(s0)
	lbu t0, 25(a1)
	slli t0, t0, 8
	lbu t1, 26(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 27(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 28(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 29(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 30(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 31(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 32(a1)
	or t0, t0, t1
	sd t0, 1232(s0)
	lbu t0, 33(a1)
	slli t0, t0, 8
	lbu t1, 34(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 35(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 36(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 37(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 38(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 39(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 40(a1)
	or t0, t0, t1
	sd t0, 1224(s0)
	lbu t0, 41(a1)
	slli t0, t0, 8
	lbu t1, 42(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 43(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 44(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 45(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 46(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 47(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 48(a1)
	or t0, t0, t1
	sd t0, 1216(s0)
	lbu t0, 0(a1)
	xori t0, t0, 4
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 83645
	addiw t0, t0, -1614
	slli t0, t0, 32
	lui t1, 740643
	addiw t1, t1, -1999
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 630256
	addiw t1, t1, -1994
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 200(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 208(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 216(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -5
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -4
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 374189
	addiw t0, t0, -944
	slli t0, t0, 32
	lui t1, 29729
	addiw t1, t1, 916
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 540296
	addiw t0, t0, -1948
	slli t0, t0, 32
	lui t1, 1031868
	addiw t1, t1, 861
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 358487
	addiw t0, t0, -1770
	slli t0, t0, 32
	lui t1, 307556
	addiw t1, t1, 168
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 611533
	addiw t0, t0, -1798
	slli t0, t0, 32
	lui t1, 998690
	addiw t1, t1, -1801
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 667032
	addiw t0, t0, -1018
	slli t0, t0, 32
	lui t1, 159772
	addiw t1, t1, -1537
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 566461
	addiw t0, t0, 1015
	slli t0, t0, 32
	lui t1, 486675
	addiw t1, t1, -1783
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 434836
	addiw t0, t0, -637
	slli t0, t0, 32
	lui t1, 437979
	addiw t1, t1, -1971
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 938942
	addiw t0, t0, 187
	slli t0, t0, 32
	lui t1, 561917
	addiw t1, t1, -1322
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 909867
	addiw t0, t0, 1317
	slli t0, t0, 32
	lui t1, 562799
	addiw t1, t1, 94
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 2
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 3
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 2
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 474255
	addiw t0, t0, -315
	slli t0, t0, 32
	lui t1, 359435
	addiw t1, t1, 305
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 879149
	addiw t0, t0, 716
	slli t0, t0, 32
	lui t1, 1043007
	addiw t1, t1, -1079
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 469021
	addiw t0, t0, -590
	slli t0, t0, 32
	lui t1, 102519
	addiw t1, t1, -1310
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1368(s0)
	addi a0, s0, 0
	call {vg_p192_check_point}
	addi s0, s3, 0
	ld a7, 1472(s0)
	ld t0, 1216(s0)
	andi t0, t0, 1
	addi t0, t0, 2
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	ld t0, 1128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	ld t0, 1120(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop

vg_ec_p192_decompress_public_key:
	.option push
	.option arch, +m, +c
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd ra, 24(a2)
	sd s3, 32(a2)
	addi s0, a2, 0
	addi s3, a2, 0
	addi s2, a0, 0
	addi t0, zero, 0
	sd t0, 1144(s0)
	lbu t0, 1(a1)
	slli t0, t0, 8
	lbu t1, 2(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 8(a1)
	or t0, t0, t1
	sd t0, 1136(s0)
	lbu t0, 9(a1)
	slli t0, t0, 8
	lbu t1, 10(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 16(a1)
	or t0, t0, t1
	sd t0, 1128(s0)
	lbu t0, 17(a1)
	slli t0, t0, 8
	lbu t1, 18(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a1)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 24(a1)
	or t0, t0, t1
	sd t0, 1120(s0)
	lbu t0, 0(a1)
	andi t0, t0, 1
	sd t0, 384(s0)
	lbu t0, 0(a1)
	xori t0, t0, 2
	srli t0, t0, 1
	addi t0, t0, -1
	srli t0, t0, 63
	addi t1, zero, 0
	sub a7, t1, t0
	sd a7, 1472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 64(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 72(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 80(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 88(s0)
	lui t0, 83645
	addiw t0, t0, -1614
	slli t0, t0, 32
	lui t1, 740643
	addiw t1, t1, -1999
	add t0, t0, t1
	sd t0, 96(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 630256
	addiw t1, t1, -1994
	add t0, t0, t1
	sd t0, 104(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 112(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 120(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 160(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 168(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 176(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 184(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 192(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 200(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 208(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 216(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 224(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 232(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	add t0, t0, t1
	sd t0, 240(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 248(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 256(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -5
	add t0, t0, t1
	sd t0, 264(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -4
	add t0, t0, t1
	sd t0, 272(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 280(s0)
	lui t0, 374189
	addiw t0, t0, -944
	slli t0, t0, 32
	lui t1, 29729
	addiw t1, t1, 916
	add t0, t0, t1
	sd t0, 288(s0)
	lui t0, 540296
	addiw t0, t0, -1948
	slli t0, t0, 32
	lui t1, 1031868
	addiw t1, t1, 861
	add t0, t0, t1
	sd t0, 296(s0)
	lui t0, 358487
	addiw t0, t0, -1770
	slli t0, t0, 32
	lui t1, 307556
	addiw t1, t1, 168
	add t0, t0, t1
	sd t0, 304(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 312(s0)
	lui t0, 611533
	addiw t0, t0, -1798
	slli t0, t0, 32
	lui t1, 998690
	addiw t1, t1, -1801
	add t0, t0, t1
	sd t0, 320(s0)
	lui t0, 667032
	addiw t0, t0, -1018
	slli t0, t0, 32
	lui t1, 159772
	addiw t1, t1, -1537
	add t0, t0, t1
	sd t0, 328(s0)
	lui t0, 566461
	addiw t0, t0, 1015
	slli t0, t0, 32
	lui t1, 486675
	addiw t1, t1, -1783
	add t0, t0, t1
	sd t0, 336(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 344(s0)
	lui t0, 434836
	addiw t0, t0, -637
	slli t0, t0, 32
	lui t1, 437979
	addiw t1, t1, -1971
	add t0, t0, t1
	sd t0, 352(s0)
	lui t0, 938942
	addiw t0, t0, 187
	slli t0, t0, 32
	lui t1, 561917
	addiw t1, t1, -1322
	add t0, t0, t1
	sd t0, 360(s0)
	lui t0, 909867
	addiw t0, t0, 1317
	slli t0, t0, 32
	lui t1, 562799
	addiw t1, t1, 94
	add t0, t0, t1
	sd t0, 368(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 376(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -3
	add t0, t0, t1
	sd t0, 448(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -2
	add t0, t0, t1
	sd t0, 456(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 464(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 472(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 2
	add t0, t0, t1
	sd t0, 1312(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 3
	add t0, t0, t1
	sd t0, 1320(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 2
	add t0, t0, t1
	sd t0, 1328(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1336(s0)
	lui t0, 474255
	addiw t0, t0, -315
	slli t0, t0, 32
	lui t1, 359435
	addiw t1, t1, 305
	add t0, t0, t1
	sd t0, 1344(s0)
	lui t0, 879149
	addiw t0, t0, 716
	slli t0, t0, 32
	lui t1, 1043007
	addiw t1, t1, -1079
	add t0, t0, t1
	sd t0, 1352(s0)
	lui t0, 469021
	addiw t0, t0, -590
	slli t0, t0, 32
	lui t1, 102519
	addiw t1, t1, -1310
	add t0, t0, t1
	sd t0, 1360(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 1368(s0)
	lui t0, 786432
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 416(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s0)
	lui t0, 262144
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 432(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 440(s0)
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1120
	addi a3, zero, 1312
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1152
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 256
	addi a3, zero, 1152
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_p192_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 800
	addi a3, zero, 1344
	call {vg_p192_add_mod_p}
	ld t0, 224(s0)
	sd t0, 992(s0)
	ld t0, 232(s0)
	sd t0, 1000(s0)
	ld t0, 240(s0)
	sd t0, 1008(s0)
	ld t0, 248(s0)
	sd t0, 1016(s0)
	addi s1, zero, 256
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 800
	addi a3, zero, 992
	call {vg_p192_mul_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 416(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 992(s0)
	ld t1, 1024(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 992(s0)
	ld t0, 1000(s0)
	ld t1, 1032(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1000(s0)
	ld t0, 1008(s0)
	ld t1, 1040(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1008(s0)
	ld t0, 1016(s0)
	ld t1, 1048(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1016(s0)
	bnez s1, 20b
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 992
	addi a3, zero, 992
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 864
	addi a3, zero, 800
	call {vg_p192_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 992
	addi a3, zero, 192
	call {vg_p192_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 160
	addi a3, zero, 672
	call {vg_p192_sub_mod_p}
	addi t3, zero, 0
	ld t4, 896(s0)
	or t3, t3, t4
	ld t4, 904(s0)
	or t3, t3, t4
	ld t4, 912(s0)
	or t3, t3, t4
	ld t4, 920(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld t0, 672(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi t1, zero, 0
	sub a7, t1, t0
	ld t0, 672(s0)
	ld t1, 704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 736(s0)
	ld t0, 680(s0)
	ld t1, 712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 744(s0)
	ld t0, 688(s0)
	ld t1, 720(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 752(s0)
	ld t0, 696(s0)
	ld t1, 728(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 760(s0)
	ld t0, 736(s0)
	ld t1, 384(s0)
	xor t0, t0, t1
	andi t0, t0, 1
	addi a7, t0, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a7, 1472(s0)
	addi t0, zero, 4
	and t0, t0, a7
	sb t0, 0(s2)
	ld t0, 1136(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 1(s2)
	srli t1, t0, 48
	sb t1, 2(s2)
	srli t1, t0, 40
	sb t1, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli t1, t0, 24
	sb t1, 5(s2)
	srli t1, t0, 16
	sb t1, 6(s2)
	srli t1, t0, 8
	sb t1, 7(s2)
	srli t1, t0, 0
	sb t1, 8(s2)
	ld t0, 1128(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 9(s2)
	srli t1, t0, 48
	sb t1, 10(s2)
	srli t1, t0, 40
	sb t1, 11(s2)
	srli t1, t0, 32
	sb t1, 12(s2)
	srli t1, t0, 24
	sb t1, 13(s2)
	srli t1, t0, 16
	sb t1, 14(s2)
	srli t1, t0, 8
	sb t1, 15(s2)
	srli t1, t0, 0
	sb t1, 16(s2)
	ld t0, 1120(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 17(s2)
	srli t1, t0, 48
	sb t1, 18(s2)
	srli t1, t0, 40
	sb t1, 19(s2)
	srli t1, t0, 32
	sb t1, 20(s2)
	srli t1, t0, 24
	sb t1, 21(s2)
	srli t1, t0, 16
	sb t1, 22(s2)
	srli t1, t0, 8
	sb t1, 23(s2)
	srli t1, t0, 0
	sb t1, 24(s2)
	ld t0, 752(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 25(s2)
	srli t1, t0, 48
	sb t1, 26(s2)
	srli t1, t0, 40
	sb t1, 27(s2)
	srli t1, t0, 32
	sb t1, 28(s2)
	srli t1, t0, 24
	sb t1, 29(s2)
	srli t1, t0, 16
	sb t1, 30(s2)
	srli t1, t0, 8
	sb t1, 31(s2)
	srli t1, t0, 0
	sb t1, 32(s2)
	ld t0, 744(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 33(s2)
	srli t1, t0, 48
	sb t1, 34(s2)
	srli t1, t0, 40
	sb t1, 35(s2)
	srli t1, t0, 32
	sb t1, 36(s2)
	srli t1, t0, 24
	sb t1, 37(s2)
	srli t1, t0, 16
	sb t1, 38(s2)
	srli t1, t0, 8
	sb t1, 39(s2)
	srli t1, t0, 0
	sb t1, 40(s2)
	ld t0, 736(s0)
	and t0, t0, a7
	srli t1, t0, 56
	sb t1, 41(s2)
	srli t1, t0, 48
	sb t1, 42(s2)
	srli t1, t0, 40
	sb t1, 43(s2)
	srli t1, t0, 32
	sb t1, 44(s2)
	srli t1, t0, 24
	sb t1, 45(s2)
	srli t1, t0, 16
	sb t1, 46(s2)
	srli t1, t0, 8
	sb t1, 47(s2)
	srli t1, t0, 0
	sb t1, 48(s2)
	ld a0, 1472(s0)
	andi a0, a0, 1
	ld ra, 24(s0)
	ld s2, 16(s0)
	ld s1, 8(s0)
	ld s3, 32(s0)
	ld s0, 0(s0)
	ret
	.option pop
