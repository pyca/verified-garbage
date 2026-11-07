// The functions of `src/internal/vg_sm4_ctr32.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1216
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
	sw t0, 40(s4)
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
	sw t0, 44(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_prepare_encrypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 20f
	srli t0, s3, 4
	beqz t0, 22f
24:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 840(s4)
	lwu t0, 36(s4)
	sw t0, 844(s4)
	lwu t0, 40(s4)
	sw t0, 848(s4)
	lwu t0, 44(s4)
	sw t0, 852(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 856(s4)
	lwu t0, 36(s4)
	sw t0, 860(s4)
	lwu t0, 40(s4)
	sw t0, 864(s4)
	lwu t0, 44(s4)
	sw t0, 868(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 872(s4)
	lwu t0, 36(s4)
	sw t0, 876(s4)
	lwu t0, 40(s4)
	sw t0, 880(s4)
	lwu t0, 44(s4)
	sw t0, 884(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 888(s4)
	lwu t0, 36(s4)
	sw t0, 892(s4)
	lwu t0, 40(s4)
	sw t0, 896(s4)
	lwu t0, 44(s4)
	sw t0, 900(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 904(s4)
	lwu t0, 36(s4)
	sw t0, 908(s4)
	lwu t0, 40(s4)
	sw t0, 912(s4)
	lwu t0, 44(s4)
	sw t0, 916(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 920(s4)
	lwu t0, 36(s4)
	sw t0, 924(s4)
	lwu t0, 40(s4)
	sw t0, 928(s4)
	lwu t0, 44(s4)
	sw t0, 932(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 936(s4)
	lwu t0, 36(s4)
	sw t0, 940(s4)
	lwu t0, 40(s4)
	sw t0, 944(s4)
	lwu t0, 44(s4)
	sw t0, 948(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 952(s4)
	lwu t0, 36(s4)
	sw t0, 956(s4)
	lwu t0, 40(s4)
	sw t0, 960(s4)
	lwu t0, 44(s4)
	sw t0, 964(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 968(s4)
	lwu t0, 36(s4)
	sw t0, 972(s4)
	lwu t0, 40(s4)
	sw t0, 976(s4)
	lwu t0, 44(s4)
	sw t0, 980(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 984(s4)
	lwu t0, 36(s4)
	sw t0, 988(s4)
	lwu t0, 40(s4)
	sw t0, 992(s4)
	lwu t0, 44(s4)
	sw t0, 996(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1000(s4)
	lwu t0, 36(s4)
	sw t0, 1004(s4)
	lwu t0, 40(s4)
	sw t0, 1008(s4)
	lwu t0, 44(s4)
	sw t0, 1012(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1016(s4)
	lwu t0, 36(s4)
	sw t0, 1020(s4)
	lwu t0, 40(s4)
	sw t0, 1024(s4)
	lwu t0, 44(s4)
	sw t0, 1028(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1032(s4)
	lwu t0, 36(s4)
	sw t0, 1036(s4)
	lwu t0, 40(s4)
	sw t0, 1040(s4)
	lwu t0, 44(s4)
	sw t0, 1044(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1048(s4)
	lwu t0, 36(s4)
	sw t0, 1052(s4)
	lwu t0, 40(s4)
	sw t0, 1056(s4)
	lwu t0, 44(s4)
	sw t0, 1060(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1064(s4)
	lwu t0, 36(s4)
	sw t0, 1068(s4)
	lwu t0, 40(s4)
	sw t0, 1072(s4)
	lwu t0, 44(s4)
	sw t0, 1076(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
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
	lwu t1, 848(s4)
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
	lwu t1, 852(s4)
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
	lwu t1, 856(s4)
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
	lwu t1, 860(s4)
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
	lwu t1, 864(s4)
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
	lwu t1, 868(s4)
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
	lwu t1, 872(s4)
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
	lwu t1, 876(s4)
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
	lwu t1, 880(s4)
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
	lwu t1, 884(s4)
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
	lwu t1, 888(s4)
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
	lwu t1, 892(s4)
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
	lwu t1, 896(s4)
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
	lwu t1, 900(s4)
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
	lwu t1, 904(s4)
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
	lwu t1, 908(s4)
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
	lwu t1, 912(s4)
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
	lwu t1, 916(s4)
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
	lwu t1, 920(s4)
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
	lwu t1, 924(s4)
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
	lwu t1, 928(s4)
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
	lwu t1, 932(s4)
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
	lwu t1, 936(s4)
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
	lwu t1, 940(s4)
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
	lwu t1, 944(s4)
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
	lwu t1, 948(s4)
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
	lwu t1, 952(s4)
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
	lwu t1, 956(s4)
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
	lwu t1, 960(s4)
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
	lwu t1, 964(s4)
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
	lwu t1, 968(s4)
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
	lwu t1, 972(s4)
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
	lwu t1, 976(s4)
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
	lwu t1, 980(s4)
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
	lwu t1, 984(s4)
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
	lwu t1, 988(s4)
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
	lwu t1, 992(s4)
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
	lwu t1, 996(s4)
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
	lwu t1, 1000(s4)
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
	lwu t1, 1004(s4)
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
	lwu t1, 1008(s4)
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
	lwu t1, 1012(s4)
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
	lwu t1, 1016(s4)
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
	lwu t1, 1020(s4)
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
	lwu t1, 1024(s4)
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
	lwu t1, 1028(s4)
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
	lwu t1, 1032(s4)
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
	lwu t1, 1036(s4)
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
	lwu t1, 1040(s4)
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
	lwu t1, 1044(s4)
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
	lwu t1, 1048(s4)
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
	lwu t1, 1052(s4)
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
	lwu t1, 1056(s4)
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
	lwu t1, 1060(s4)
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
	lwu t1, 1064(s4)
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
	lwu t1, 1068(s4)
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
	lwu t1, 1072(s4)
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
	lwu t1, 1076(s4)
	xor t0, t0, t1
	sb t0, 252(s2)
	srli t2, t0, 8
	sb t2, 253(s2)
	srli t2, t0, 16
	sb t2, 254(s2)
	srli t2, t0, 24
	sb t2, 255(s2)
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 24b
	j 23f
22:
23:
	beqz s3, 25f
27:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 27b
	j 26f
25:
26:
	j 21f
20:
	srli t0, s3, 4
	beqz t0, 28f
210:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 840(s4)
	lwu t0, 36(s4)
	sw t0, 844(s4)
	lwu t0, 40(s4)
	sw t0, 848(s4)
	lwu t0, 44(s4)
	sw t0, 852(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 856(s4)
	lwu t0, 36(s4)
	sw t0, 860(s4)
	lwu t0, 40(s4)
	sw t0, 864(s4)
	lwu t0, 44(s4)
	sw t0, 868(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 872(s4)
	lwu t0, 36(s4)
	sw t0, 876(s4)
	lwu t0, 40(s4)
	sw t0, 880(s4)
	lwu t0, 44(s4)
	sw t0, 884(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 888(s4)
	lwu t0, 36(s4)
	sw t0, 892(s4)
	lwu t0, 40(s4)
	sw t0, 896(s4)
	lwu t0, 44(s4)
	sw t0, 900(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 904(s4)
	lwu t0, 36(s4)
	sw t0, 908(s4)
	lwu t0, 40(s4)
	sw t0, 912(s4)
	lwu t0, 44(s4)
	sw t0, 916(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 920(s4)
	lwu t0, 36(s4)
	sw t0, 924(s4)
	lwu t0, 40(s4)
	sw t0, 928(s4)
	lwu t0, 44(s4)
	sw t0, 932(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 936(s4)
	lwu t0, 36(s4)
	sw t0, 940(s4)
	lwu t0, 40(s4)
	sw t0, 944(s4)
	lwu t0, 44(s4)
	sw t0, 948(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 952(s4)
	lwu t0, 36(s4)
	sw t0, 956(s4)
	lwu t0, 40(s4)
	sw t0, 960(s4)
	lwu t0, 44(s4)
	sw t0, 964(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 968(s4)
	lwu t0, 36(s4)
	sw t0, 972(s4)
	lwu t0, 40(s4)
	sw t0, 976(s4)
	lwu t0, 44(s4)
	sw t0, 980(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 984(s4)
	lwu t0, 36(s4)
	sw t0, 988(s4)
	lwu t0, 40(s4)
	sw t0, 992(s4)
	lwu t0, 44(s4)
	sw t0, 996(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1000(s4)
	lwu t0, 36(s4)
	sw t0, 1004(s4)
	lwu t0, 40(s4)
	sw t0, 1008(s4)
	lwu t0, 44(s4)
	sw t0, 1012(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1016(s4)
	lwu t0, 36(s4)
	sw t0, 1020(s4)
	lwu t0, 40(s4)
	sw t0, 1024(s4)
	lwu t0, 44(s4)
	sw t0, 1028(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1032(s4)
	lwu t0, 36(s4)
	sw t0, 1036(s4)
	lwu t0, 40(s4)
	sw t0, 1040(s4)
	lwu t0, 44(s4)
	sw t0, 1044(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1048(s4)
	lwu t0, 36(s4)
	sw t0, 1052(s4)
	lwu t0, 40(s4)
	sw t0, 1056(s4)
	lwu t0, 44(s4)
	sw t0, 1060(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 1064(s4)
	lwu t0, 36(s4)
	sw t0, 1068(s4)
	lwu t0, 40(s4)
	sw t0, 1072(s4)
	lwu t0, 44(s4)
	sw t0, 1076(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 880(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 884(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 888(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 892(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 896(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 900(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 904(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 908(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 912(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 916(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 920(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 924(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 928(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 932(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 936(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 940(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 944(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 948(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	lwu t0, 128(s2)
	lwu t1, 952(s4)
	xor t0, t0, t1
	sw t0, 128(s2)
	lwu t0, 132(s2)
	lwu t1, 956(s4)
	xor t0, t0, t1
	sw t0, 132(s2)
	lwu t0, 136(s2)
	lwu t1, 960(s4)
	xor t0, t0, t1
	sw t0, 136(s2)
	lwu t0, 140(s2)
	lwu t1, 964(s4)
	xor t0, t0, t1
	sw t0, 140(s2)
	lwu t0, 144(s2)
	lwu t1, 968(s4)
	xor t0, t0, t1
	sw t0, 144(s2)
	lwu t0, 148(s2)
	lwu t1, 972(s4)
	xor t0, t0, t1
	sw t0, 148(s2)
	lwu t0, 152(s2)
	lwu t1, 976(s4)
	xor t0, t0, t1
	sw t0, 152(s2)
	lwu t0, 156(s2)
	lwu t1, 980(s4)
	xor t0, t0, t1
	sw t0, 156(s2)
	lwu t0, 160(s2)
	lwu t1, 984(s4)
	xor t0, t0, t1
	sw t0, 160(s2)
	lwu t0, 164(s2)
	lwu t1, 988(s4)
	xor t0, t0, t1
	sw t0, 164(s2)
	lwu t0, 168(s2)
	lwu t1, 992(s4)
	xor t0, t0, t1
	sw t0, 168(s2)
	lwu t0, 172(s2)
	lwu t1, 996(s4)
	xor t0, t0, t1
	sw t0, 172(s2)
	lwu t0, 176(s2)
	lwu t1, 1000(s4)
	xor t0, t0, t1
	sw t0, 176(s2)
	lwu t0, 180(s2)
	lwu t1, 1004(s4)
	xor t0, t0, t1
	sw t0, 180(s2)
	lwu t0, 184(s2)
	lwu t1, 1008(s4)
	xor t0, t0, t1
	sw t0, 184(s2)
	lwu t0, 188(s2)
	lwu t1, 1012(s4)
	xor t0, t0, t1
	sw t0, 188(s2)
	lwu t0, 192(s2)
	lwu t1, 1016(s4)
	xor t0, t0, t1
	sw t0, 192(s2)
	lwu t0, 196(s2)
	lwu t1, 1020(s4)
	xor t0, t0, t1
	sw t0, 196(s2)
	lwu t0, 200(s2)
	lwu t1, 1024(s4)
	xor t0, t0, t1
	sw t0, 200(s2)
	lwu t0, 204(s2)
	lwu t1, 1028(s4)
	xor t0, t0, t1
	sw t0, 204(s2)
	lwu t0, 208(s2)
	lwu t1, 1032(s4)
	xor t0, t0, t1
	sw t0, 208(s2)
	lwu t0, 212(s2)
	lwu t1, 1036(s4)
	xor t0, t0, t1
	sw t0, 212(s2)
	lwu t0, 216(s2)
	lwu t1, 1040(s4)
	xor t0, t0, t1
	sw t0, 216(s2)
	lwu t0, 220(s2)
	lwu t1, 1044(s4)
	xor t0, t0, t1
	sw t0, 220(s2)
	lwu t0, 224(s2)
	lwu t1, 1048(s4)
	xor t0, t0, t1
	sw t0, 224(s2)
	lwu t0, 228(s2)
	lwu t1, 1052(s4)
	xor t0, t0, t1
	sw t0, 228(s2)
	lwu t0, 232(s2)
	lwu t1, 1056(s4)
	xor t0, t0, t1
	sw t0, 232(s2)
	lwu t0, 236(s2)
	lwu t1, 1060(s4)
	xor t0, t0, t1
	sw t0, 236(s2)
	lwu t0, 240(s2)
	lwu t1, 1064(s4)
	xor t0, t0, t1
	sw t0, 240(s2)
	lwu t0, 244(s2)
	lwu t1, 1068(s4)
	xor t0, t0, t1
	sw t0, 244(s2)
	lwu t0, 248(s2)
	lwu t1, 1072(s4)
	xor t0, t0, t1
	sw t0, 248(s2)
	lwu t0, 252(s2)
	lwu t1, 1076(s4)
	xor t0, t0, t1
	sw t0, 252(s2)
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 210b
	j 29f
28:
29:
	beqz s3, 211f
213:
	lwu t0, 32(s4)
	sw t0, 824(s4)
	lwu t0, 36(s4)
	sw t0, 828(s4)
	lwu t0, 40(s4)
	sw t0, 832(s4)
	lwu t0, 44(s4)
	sw t0, 836(s4)
	addi t1, zero, 1
	lbu t0, 47(s4)
	add t0, t0, t1
	sb t0, 47(s4)
	srli t1, t0, 8
	lbu t0, 46(s4)
	add t0, t0, t1
	sb t0, 46(s4)
	srli t1, t0, 8
	lbu t0, 45(s4)
	add t0, t0, t1
	sb t0, 45(s4)
	srli t1, t0, 8
	lbu t0, 44(s4)
	add t0, t0, t1
	sb t0, 44(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 213b
	j 212f
211:
212:
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
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 406
214:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 214b
	addi sp, sp, 1216
	addi sp, sp, 2032
	ret
	.option pop
