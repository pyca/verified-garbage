// The functions of `src/internal/vg_camellia_ctr_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr_core:
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
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
27:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 27b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
28:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 28b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 26b
	j 25f
24:
25:
	srli t0, s3, 2
	beqz t0, 29f
211:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
212:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 212b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
213:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 213b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 211b
	j 210f
29:
210:
	srli t0, s3, 1
	beqz t0, 214f
216:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
217:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 217b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
218:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 218b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 216b
	j 215f
214:
215:
	beqz s3, 219f
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
	bnez s3, 221b
	j 220f
219:
220:
	j 23f
22:
	srli t0, s3, 3
	beqz t0, 222f
224:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
225:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 225b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
226:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 226b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 224b
	j 223f
222:
223:
	srli t0, s3, 2
	beqz t0, 227f
229:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
230:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 230b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
231:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 231b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 229b
	j 228f
227:
228:
	srli t0, s3, 1
	beqz t0, 232f
234:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
235:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 235b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
236:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 236b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 234b
	j 233f
232:
233:
	beqz s3, 237f
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
	bnez s3, 239b
	j 238f
237:
238:
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
240:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 240b
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
	beqz t0, 241f
	srli t0, s3, 3
	beqz t0, 243f
245:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
246:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 246b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
247:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 247b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 245b
	j 244f
243:
244:
	srli t0, s3, 2
	beqz t0, 248f
250:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
251:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 251b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
252:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 252b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 250b
	j 249f
248:
249:
	srli t0, s3, 1
	beqz t0, 253f
255:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
256:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 256b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
257:
	lbu t0, 0(t4)
	lbu t2, 1(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 0(t3)
	xor t0, t0, t1
	sb t0, 0(t4)
	srli t2, t0, 8
	sb t2, 1(t4)
	srli t2, t0, 16
	sb t2, 2(t4)
	srli t2, t0, 24
	sb t2, 3(t4)
	lbu t0, 4(t4)
	lbu t2, 5(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 4(t3)
	xor t0, t0, t1
	sb t0, 4(t4)
	srli t2, t0, 8
	sb t2, 5(t4)
	srli t2, t0, 16
	sb t2, 6(t4)
	srli t2, t0, 24
	sb t2, 7(t4)
	lbu t0, 8(t4)
	lbu t2, 9(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 8(t3)
	xor t0, t0, t1
	sb t0, 8(t4)
	srli t2, t0, 8
	sb t2, 9(t4)
	srli t2, t0, 16
	sb t2, 10(t4)
	srli t2, t0, 24
	sb t2, 11(t4)
	lbu t0, 12(t4)
	lbu t2, 13(t4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(t4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(t4)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 12(t3)
	xor t0, t0, t1
	sb t0, 12(t4)
	srli t2, t0, 8
	sb t2, 13(t4)
	srli t2, t0, 16
	sb t2, 14(t4)
	srli t2, t0, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 257b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 255b
	j 254f
253:
254:
	beqz s3, 258f
260:
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
	bnez s3, 260b
	j 259f
258:
259:
	j 242f
241:
	srli t0, s3, 3
	beqz t0, 261f
263:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
264:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 264b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 8
265:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 265b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 263b
	j 262f
261:
262:
	srli t0, s3, 2
	beqz t0, 266f
268:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
269:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 269b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 4
270:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 270b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 268b
	j 267f
266:
267:
	srli t0, s3, 1
	beqz t0, 271f
273:
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
274:
	lwu t0, 32(s4)
	sw t0, 0(t3)
	lwu t0, 36(s4)
	sw t0, 4(t3)
	lwu t0, 40(s4)
	sw t0, 8(t3)
	lwu t0, 44(s4)
	sw t0, 12(t3)
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
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 274b
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t3, s4, 816
	addi t4, s2, 0
	addi t5, zero, 2
275:
	lwu t0, 0(t4)
	lwu t1, 0(t3)
	xor t0, t0, t1
	sw t0, 0(t4)
	lwu t0, 4(t4)
	lwu t1, 4(t3)
	xor t0, t0, t1
	sw t0, 4(t4)
	lwu t0, 8(t4)
	lwu t1, 8(t3)
	xor t0, t0, t1
	sw t0, 8(t4)
	lwu t0, 12(t4)
	lwu t1, 12(t3)
	xor t0, t0, t1
	sw t0, 12(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 275b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 273b
	j 272f
271:
272:
	beqz s3, 276f
278:
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
	bnez s3, 278b
	j 277f
276:
277:
242:
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
279:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 279b
	addi sp, sp, 1232
	addi sp, sp, 2032
21:
	ret
	.option pop
