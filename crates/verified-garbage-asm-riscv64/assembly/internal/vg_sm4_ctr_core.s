// The functions of `src/internal/vg_sm4_ctr_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr_core:
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
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 16
25:
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
	bnez t5, 25b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 16
26:
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
	bnez t5, 26b
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 24b
	j 23f
22:
23:
	srli t0, s3, 3
	beqz t0, 27f
29:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 8
210:
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
	bnez t5, 210b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 8
211:
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
	bnez t5, 211b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 29b
	j 28f
27:
28:
	srli t0, s3, 2
	beqz t0, 212f
214:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 4
215:
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
	bnez t5, 215b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 4
216:
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
	bnez t5, 216b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 214b
	j 213f
212:
213:
	srli t0, s3, 1
	beqz t0, 217f
219:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 2
220:
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
	bnez t5, 220b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 2
221:
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
	bnez t5, 221b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 219b
	j 218f
217:
218:
	beqz s3, 222f
224:
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
	bnez s3, 224b
	j 223f
222:
223:
	j 21f
20:
	srli t0, s3, 4
	beqz t0, 225f
227:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 16
228:
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
	bnez t5, 228b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 16
229:
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
	bnez t5, 229b
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 227b
	j 226f
225:
226:
	srli t0, s3, 3
	beqz t0, 230f
232:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 8
233:
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
	bnez t5, 233b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 8
234:
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
	bnez t5, 234b
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 232b
	j 231f
230:
231:
	srli t0, s3, 2
	beqz t0, 235f
237:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 4
238:
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
	bnez t5, 238b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 4
239:
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
	bnez t5, 239b
	addi s2, s2, 64
	addi s3, s3, -4
	srli t0, s3, 2
	bnez t0, 237b
	j 236f
235:
236:
	srli t0, s3, 1
	beqz t0, 240f
242:
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 2
243:
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
	bnez t5, 243b
	addi t6, s4, 2032
	addi t6, t6, 1200
	sd ra, 0(t6)
	call {vg_sm4_modes_crypt}
	addi t6, s4, 2032
	addi t6, t6, 1200
	ld ra, 0(t6)
	addi t3, s4, 824
	addi t4, s2, 0
	addi t5, zero, 2
244:
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
	bnez t5, 244b
	addi s2, s2, 32
	addi s3, s3, -2
	srli t0, s3, 1
	bnez t0, 242b
	j 241f
240:
241:
	beqz s3, 245f
247:
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
	bnez s3, 247b
	j 246f
245:
246:
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
248:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 248b
	addi sp, sp, 1216
	addi sp, sp, 2032
	ret
	.option pop
