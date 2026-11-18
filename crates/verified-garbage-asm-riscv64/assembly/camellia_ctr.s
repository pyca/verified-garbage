// The functions of `src/camellia_ctr.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -18
	beqz t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -1232
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
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 22f
	srli t0, s3, 3
	beqz t0, 24f
26:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 880(s4)
	lwu t0, 36(s4)
	sw t0, 884(s4)
	lwu t0, 40(s4)
	sw t0, 888(s4)
	lwu t0, 44(s4)
	sw t0, 892(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 896(s4)
	lwu t0, 36(s4)
	sw t0, 900(s4)
	lwu t0, 40(s4)
	sw t0, 904(s4)
	lwu t0, 44(s4)
	sw t0, 908(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 912(s4)
	lwu t0, 36(s4)
	sw t0, 916(s4)
	lwu t0, 40(s4)
	sw t0, 920(s4)
	lwu t0, 44(s4)
	sw t0, 924(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 928(s4)
	lwu t0, 36(s4)
	sw t0, 932(s4)
	lwu t0, 40(s4)
	sw t0, 936(s4)
	lwu t0, 44(s4)
	sw t0, 940(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
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
	lwu t1, 848(s4)
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
	lwu t1, 852(s4)
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
	lwu t1, 856(s4)
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
	lwu t1, 860(s4)
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
	lwu t1, 864(s4)
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
	lwu t1, 868(s4)
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
	lwu t1, 872(s4)
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
	lwu t1, 876(s4)
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
	lwu t1, 880(s4)
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
	lwu t1, 884(s4)
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
	lwu t1, 888(s4)
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
	lwu t1, 892(s4)
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
	lwu t1, 896(s4)
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
	lwu t1, 900(s4)
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
	lwu t1, 904(s4)
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
	lwu t1, 908(s4)
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
	lwu t1, 912(s4)
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
	lwu t1, 916(s4)
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
	lwu t1, 920(s4)
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
	lwu t1, 924(s4)
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
	lwu t1, 928(s4)
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
	lwu t1, 932(s4)
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
	lwu t1, 936(s4)
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
	lwu t1, 940(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 26b
	j 25f
24:
25:
	srli t0, s3, 2
	beqz t0, 27f
29:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
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
	lwu t1, 848(s4)
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
	lwu t1, 852(s4)
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
	lwu t1, 856(s4)
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
	lwu t1, 860(s4)
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
	lwu t1, 864(s4)
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
	lwu t1, 868(s4)
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
	lwu t1, 872(s4)
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
	lwu t1, 876(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 29b
	j 28f
27:
28:
	srli t0, s3, 1
	beqz t0, 210f
212:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 212b
	j 211f
210:
211:
	beqz s3, 213f
215:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	bnez s3, 215b
	j 214f
213:
214:
	j 23f
22:
	srli t0, s3, 3
	beqz t0, 216f
218:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 880(s4)
	lwu t0, 36(s4)
	sw t0, 884(s4)
	lwu t0, 40(s4)
	sw t0, 888(s4)
	lwu t0, 44(s4)
	sw t0, 892(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 896(s4)
	lwu t0, 36(s4)
	sw t0, 900(s4)
	lwu t0, 40(s4)
	sw t0, 904(s4)
	lwu t0, 44(s4)
	sw t0, 908(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 912(s4)
	lwu t0, 36(s4)
	sw t0, 916(s4)
	lwu t0, 40(s4)
	sw t0, 920(s4)
	lwu t0, 44(s4)
	sw t0, 924(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 928(s4)
	lwu t0, 36(s4)
	sw t0, 932(s4)
	lwu t0, 40(s4)
	sw t0, 936(s4)
	lwu t0, 44(s4)
	sw t0, 940(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 880(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 884(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 888(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 892(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 896(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 900(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 904(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 908(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 912(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 916(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 920(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 924(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 928(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 932(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 936(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 940(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 218b
	j 217f
216:
217:
	srli t0, s3, 2
	beqz t0, 219f
221:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 221b
	j 220f
219:
220:
	srli t0, s3, 1
	beqz t0, 222f
224:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 224b
	j 223f
222:
223:
	beqz s3, 225f
227:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 227b
	j 226f
225:
226:
23:
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
	addi t2, zero, 408
228:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 228b
	addi sp, sp, 1232
	addi sp, sp, 2032
	j 21f
20:
	addi sp, sp, -2032
	addi sp, sp, -1232
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
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 229f
	srli t0, s3, 3
	beqz t0, 231f
233:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 880(s4)
	lwu t0, 36(s4)
	sw t0, 884(s4)
	lwu t0, 40(s4)
	sw t0, 888(s4)
	lwu t0, 44(s4)
	sw t0, 892(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 896(s4)
	lwu t0, 36(s4)
	sw t0, 900(s4)
	lwu t0, 40(s4)
	sw t0, 904(s4)
	lwu t0, 44(s4)
	sw t0, 908(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 912(s4)
	lwu t0, 36(s4)
	sw t0, 916(s4)
	lwu t0, 40(s4)
	sw t0, 920(s4)
	lwu t0, 44(s4)
	sw t0, 924(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 928(s4)
	lwu t0, 36(s4)
	sw t0, 932(s4)
	lwu t0, 40(s4)
	sw t0, 936(s4)
	lwu t0, 44(s4)
	sw t0, 940(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
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
	lwu t1, 848(s4)
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
	lwu t1, 852(s4)
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
	lwu t1, 856(s4)
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
	lwu t1, 860(s4)
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
	lwu t1, 864(s4)
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
	lwu t1, 868(s4)
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
	lwu t1, 872(s4)
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
	lwu t1, 876(s4)
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
	lwu t1, 880(s4)
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
	lwu t1, 884(s4)
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
	lwu t1, 888(s4)
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
	lwu t1, 892(s4)
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
	lwu t1, 896(s4)
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
	lwu t1, 900(s4)
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
	lwu t1, 904(s4)
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
	lwu t1, 908(s4)
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
	lwu t1, 912(s4)
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
	lwu t1, 916(s4)
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
	lwu t1, 920(s4)
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
	lwu t1, 924(s4)
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
	lwu t1, 928(s4)
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
	lwu t1, 932(s4)
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
	lwu t1, 936(s4)
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
	lwu t1, 940(s4)
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 233b
	j 232f
231:
232:
	srli t0, s3, 2
	beqz t0, 234f
236:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
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
	lwu t1, 848(s4)
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
	lwu t1, 852(s4)
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
	lwu t1, 856(s4)
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
	lwu t1, 860(s4)
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
	lwu t1, 864(s4)
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
	lwu t1, 868(s4)
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
	lwu t1, 872(s4)
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
	lwu t1, 876(s4)
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 236b
	j 235f
234:
235:
	srli t0, s3, 1
	beqz t0, 237f
239:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	lwu t1, 832(s4)
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
	lwu t1, 836(s4)
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
	lwu t1, 840(s4)
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
	lwu t1, 844(s4)
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 239b
	j 238f
237:
238:
	beqz s3, 240f
242:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
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
	lwu t1, 816(s4)
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
	lwu t1, 820(s4)
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
	lwu t1, 824(s4)
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
	lwu t1, 828(s4)
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
	bnez s3, 242b
	j 241f
240:
241:
	j 230f
229:
	srli t0, s3, 3
	beqz t0, 243f
245:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 880(s4)
	lwu t0, 36(s4)
	sw t0, 884(s4)
	lwu t0, 40(s4)
	sw t0, 888(s4)
	lwu t0, 44(s4)
	sw t0, 892(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 896(s4)
	lwu t0, 36(s4)
	sw t0, 900(s4)
	lwu t0, 40(s4)
	sw t0, 904(s4)
	lwu t0, 44(s4)
	sw t0, 908(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 912(s4)
	lwu t0, 36(s4)
	sw t0, 916(s4)
	lwu t0, 40(s4)
	sw t0, 920(s4)
	lwu t0, 44(s4)
	sw t0, 924(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 928(s4)
	lwu t0, 36(s4)
	sw t0, 932(s4)
	lwu t0, 40(s4)
	sw t0, 936(s4)
	lwu t0, 44(s4)
	sw t0, 940(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	lwu t0, 64(s2)
	lwu t1, 880(s4)
	xor t0, t0, t1
	sw t0, 64(s2)
	lwu t0, 68(s2)
	lwu t1, 884(s4)
	xor t0, t0, t1
	sw t0, 68(s2)
	lwu t0, 72(s2)
	lwu t1, 888(s4)
	xor t0, t0, t1
	sw t0, 72(s2)
	lwu t0, 76(s2)
	lwu t1, 892(s4)
	xor t0, t0, t1
	sw t0, 76(s2)
	lwu t0, 80(s2)
	lwu t1, 896(s4)
	xor t0, t0, t1
	sw t0, 80(s2)
	lwu t0, 84(s2)
	lwu t1, 900(s4)
	xor t0, t0, t1
	sw t0, 84(s2)
	lwu t0, 88(s2)
	lwu t1, 904(s4)
	xor t0, t0, t1
	sw t0, 88(s2)
	lwu t0, 92(s2)
	lwu t1, 908(s4)
	xor t0, t0, t1
	sw t0, 92(s2)
	lwu t0, 96(s2)
	lwu t1, 912(s4)
	xor t0, t0, t1
	sw t0, 96(s2)
	lwu t0, 100(s2)
	lwu t1, 916(s4)
	xor t0, t0, t1
	sw t0, 100(s2)
	lwu t0, 104(s2)
	lwu t1, 920(s4)
	xor t0, t0, t1
	sw t0, 104(s2)
	lwu t0, 108(s2)
	lwu t1, 924(s4)
	xor t0, t0, t1
	sw t0, 108(s2)
	lwu t0, 112(s2)
	lwu t1, 928(s4)
	xor t0, t0, t1
	sw t0, 112(s2)
	lwu t0, 116(s2)
	lwu t1, 932(s4)
	xor t0, t0, t1
	sw t0, 116(s2)
	lwu t0, 120(s2)
	lwu t1, 936(s4)
	xor t0, t0, t1
	sw t0, 120(s2)
	lwu t0, 124(s2)
	lwu t1, 940(s4)
	xor t0, t0, t1
	sw t0, 124(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 245b
	j 244f
243:
244:
	srli t0, s3, 2
	beqz t0, 246f
248:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 848(s4)
	lwu t0, 36(s4)
	sw t0, 852(s4)
	lwu t0, 40(s4)
	sw t0, 856(s4)
	lwu t0, 44(s4)
	sw t0, 860(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 864(s4)
	lwu t0, 36(s4)
	sw t0, 868(s4)
	lwu t0, 40(s4)
	sw t0, 872(s4)
	lwu t0, 44(s4)
	sw t0, 876(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	lwu t0, 32(s2)
	lwu t1, 848(s4)
	xor t0, t0, t1
	sw t0, 32(s2)
	lwu t0, 36(s2)
	lwu t1, 852(s4)
	xor t0, t0, t1
	sw t0, 36(s2)
	lwu t0, 40(s2)
	lwu t1, 856(s4)
	xor t0, t0, t1
	sw t0, 40(s2)
	lwu t0, 44(s2)
	lwu t1, 860(s4)
	xor t0, t0, t1
	sw t0, 44(s2)
	lwu t0, 48(s2)
	lwu t1, 864(s4)
	xor t0, t0, t1
	sw t0, 48(s2)
	lwu t0, 52(s2)
	lwu t1, 868(s4)
	xor t0, t0, t1
	sw t0, 52(s2)
	lwu t0, 56(s2)
	lwu t1, 872(s4)
	xor t0, t0, t1
	sw t0, 56(s2)
	lwu t0, 60(s2)
	lwu t1, 876(s4)
	xor t0, t0, t1
	sw t0, 60(s2)
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 248b
	j 247f
246:
247:
	srli t0, s3, 1
	beqz t0, 249f
251:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	lwu t0, 32(s4)
	sw t0, 832(s4)
	lwu t0, 36(s4)
	sw t0, 836(s4)
	lwu t0, 40(s4)
	sw t0, 840(s4)
	lwu t0, 44(s4)
	sw t0, 844(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	lwu t0, 16(s2)
	lwu t1, 832(s4)
	xor t0, t0, t1
	sw t0, 16(s2)
	lwu t0, 20(s2)
	lwu t1, 836(s4)
	xor t0, t0, t1
	sw t0, 20(s2)
	lwu t0, 24(s2)
	lwu t1, 840(s4)
	xor t0, t0, t1
	sw t0, 24(s2)
	lwu t0, 28(s2)
	lwu t1, 844(s4)
	xor t0, t0, t1
	sw t0, 28(s2)
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 251b
	j 250f
249:
250:
	beqz s3, 252f
254:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
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
	lbu t0, 43(s4)
	add t0, t0, t1
	sb t0, 43(s4)
	srli t1, t0, 8
	lbu t0, 42(s4)
	add t0, t0, t1
	sb t0, 42(s4)
	srli t1, t0, 8
	lbu t0, 41(s4)
	add t0, t0, t1
	sb t0, 41(s4)
	srli t1, t0, 8
	lbu t0, 40(s4)
	add t0, t0, t1
	sb t0, 40(s4)
	srli t1, t0, 8
	lbu t0, 39(s4)
	add t0, t0, t1
	sb t0, 39(s4)
	srli t1, t0, 8
	lbu t0, 38(s4)
	add t0, t0, t1
	sb t0, 38(s4)
	srli t1, t0, 8
	lbu t0, 37(s4)
	add t0, t0, t1
	sb t0, 37(s4)
	srli t1, t0, 8
	lbu t0, 36(s4)
	add t0, t0, t1
	sb t0, 36(s4)
	srli t1, t0, 8
	lbu t0, 35(s4)
	add t0, t0, t1
	sb t0, 35(s4)
	srli t1, t0, 8
	lbu t0, 34(s4)
	add t0, t0, t1
	sb t0, 34(s4)
	srli t1, t0, 8
	lbu t0, 33(s4)
	add t0, t0, t1
	sb t0, 33(s4)
	srli t1, t0, 8
	lbu t0, 32(s4)
	add t0, t0, t1
	sb t0, 32(s4)
	srli t1, t0, 8
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 254b
	j 253f
252:
253:
230:
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
	addi t2, zero, 408
255:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 255b
	addi sp, sp, 1232
	addi sp, sp, 2032
21:
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -1216
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	addi sp, sp, 1216
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_camellia_ctr_final:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi a5, sp, 0
	sd ra, 0(a5)
	sd s1, 8(a5)
	sd s2, 16(a5)
	sd s3, 24(a5)
	sd s4, 32(a5)
	sd s5, 40(a5)
	sd s6, 48(a5)
	sd s7, 56(a5)
	addi s1, a0, 0
	addi s4, a1, 0
	addi s5, a2, 0
	addi s7, a5, 0
	srli t0, a4, 4
	slli t1, t0, 4
	add s2, a3, t1
	sub s3, a4, t1
	addi a4, t0, 0
	call {vg_camellia_ctr_core}
	beqz s3, 20f
	addi t0, zero, 0
	sd t0, 64(s7)
	sd t0, 72(s7)
	addi a0, s1, 0
	addi a1, s4, 0
	addi a2, s5, 0
	addi a3, s7, 64
	addi a4, zero, 1
	call {vg_camellia_ctr_core}
	addi t2, s7, 64
22:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 22b
	j 21f
20:
21:
	ld ra, 0(s7)
	ld s1, 8(s7)
	ld s2, 16(s7)
	ld s3, 24(s7)
	ld s4, 32(s7)
	ld s5, 40(s7)
	ld s6, 48(s7)
	ld s7, 56(s7)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	addi sp, sp, 80
	ret
	.option pop
