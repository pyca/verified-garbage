// The functions of `src/aes_xts.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_unit:
	.option push
	.option arch, +m, +c
	addi t0, a6, 39
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	addi s1, a0, 0
	addi s2, a2, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a6, 0
	lbu t3, 0(a3)
	sb t3, 0(s6)
	lbu t3, 1(a3)
	sb t3, 1(s6)
	lbu t3, 2(a3)
	sb t3, 2(s6)
	lbu t3, 3(a3)
	sb t3, 3(s6)
	lbu t3, 4(a3)
	sb t3, 4(s6)
	lbu t3, 5(a3)
	sb t3, 5(s6)
	lbu t3, 6(a3)
	sb t3, 6(s6)
	lbu t3, 7(a3)
	sb t3, 7(s6)
	lbu t3, 8(a3)
	sb t3, 8(s6)
	lbu t3, 9(a3)
	sb t3, 9(s6)
	lbu t3, 10(a3)
	sb t3, 10(s6)
	lbu t3, 11(a3)
	sb t3, 11(s6)
	lbu t3, 12(a3)
	sb t3, 12(s6)
	lbu t3, 13(a3)
	sb t3, 13(s6)
	lbu t3, 14(a3)
	sb t3, 14(s6)
	lbu t3, 15(a3)
	sb t3, 15(s6)
	addi t1, zero, 0
	sb t1, 16(s6)
	addi t1, zero, 0
	sb t1, 17(s6)
	addi t1, zero, 0
	sb t1, 18(s6)
	addi t1, zero, 0
	sb t1, 19(s6)
	addi t1, zero, 0
	sb t1, 20(s6)
	addi t1, zero, 0
	sb t1, 21(s6)
	addi t1, zero, 0
	sb t1, 22(s6)
	addi t1, zero, 0
	sb t1, 23(s6)
	addi t1, zero, 0
	sb t1, 24(s6)
	addi t1, zero, 0
	sb t1, 25(s6)
	addi t1, zero, 0
	sb t1, 26(s6)
	addi t1, zero, 0
	sb t1, 27(s6)
	addi t1, zero, 0
	sb t1, 28(s6)
	addi t1, zero, 0
	sb t1, 29(s6)
	addi t1, zero, 0
	sb t1, 30(s6)
	addi t1, zero, 0
	sb t1, 31(s6)
	addi a0, a1, 0
	addi a1, s2, 0
	addi a2, s6, 16
	addi a3, s6, 0
	addi a4, zero, 1
	addi a5, s6, 96
	call {vg_aes_xts_encrypt}
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 0
	addi a3, s4, 0
	srli a4, s5, 4
	addi a5, s6, 96
	call {vg_aes_xts_encrypt}
	srli t1, s5, 4
	slli t1, t1, 4
	sub t2, s5, t1
	beqz t2, 20f
	add t3, s4, t1
	addi t3, t3, -16
22:
	lbu t4, 0(t3)
	lbu t5, 16(t3)
	sb t5, 0(t3)
	sb t4, 16(t3)
	addi t3, t3, 1
	addi t2, t2, -1
	bnez t2, 22b
	add a3, s4, t1
	addi a3, a3, -16
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 0
	addi a4, zero, 1
	addi a5, s6, 96
	call {vg_aes_xts_encrypt}
	j 21f
20:
21:
	addi t0, s6, 39
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ret
	.option pop

vg_aes_xts_decrypt_unit:
	.option push
	.option arch, +m, +c
	addi t0, a6, 39
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	addi s1, a0, 0
	addi s2, a2, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a6, 0
	lbu t3, 0(a3)
	sb t3, 0(s6)
	lbu t3, 1(a3)
	sb t3, 1(s6)
	lbu t3, 2(a3)
	sb t3, 2(s6)
	lbu t3, 3(a3)
	sb t3, 3(s6)
	lbu t3, 4(a3)
	sb t3, 4(s6)
	lbu t3, 5(a3)
	sb t3, 5(s6)
	lbu t3, 6(a3)
	sb t3, 6(s6)
	lbu t3, 7(a3)
	sb t3, 7(s6)
	lbu t3, 8(a3)
	sb t3, 8(s6)
	lbu t3, 9(a3)
	sb t3, 9(s6)
	lbu t3, 10(a3)
	sb t3, 10(s6)
	lbu t3, 11(a3)
	sb t3, 11(s6)
	lbu t3, 12(a3)
	sb t3, 12(s6)
	lbu t3, 13(a3)
	sb t3, 13(s6)
	lbu t3, 14(a3)
	sb t3, 14(s6)
	lbu t3, 15(a3)
	sb t3, 15(s6)
	addi t1, zero, 0
	sb t1, 16(s6)
	addi t1, zero, 0
	sb t1, 17(s6)
	addi t1, zero, 0
	sb t1, 18(s6)
	addi t1, zero, 0
	sb t1, 19(s6)
	addi t1, zero, 0
	sb t1, 20(s6)
	addi t1, zero, 0
	sb t1, 21(s6)
	addi t1, zero, 0
	sb t1, 22(s6)
	addi t1, zero, 0
	sb t1, 23(s6)
	addi t1, zero, 0
	sb t1, 24(s6)
	addi t1, zero, 0
	sb t1, 25(s6)
	addi t1, zero, 0
	sb t1, 26(s6)
	addi t1, zero, 0
	sb t1, 27(s6)
	addi t1, zero, 0
	sb t1, 28(s6)
	addi t1, zero, 0
	sb t1, 29(s6)
	addi t1, zero, 0
	sb t1, 30(s6)
	addi t1, zero, 0
	sb t1, 31(s6)
	addi a0, a1, 0
	addi a1, s2, 0
	addi a2, s6, 16
	addi a3, s6, 0
	addi a4, zero, 1
	addi a5, s6, 96
	call {vg_aes_xts_encrypt}
	srli t1, s5, 4
	slli t1, t1, 4
	sub t2, s5, t1
	beqz t2, 20f
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 0
	addi a3, s4, 0
	srli a4, s5, 4
	addi a5, s6, 96
	addi a4, a4, -1
	call {vg_aes_xts_decrypt}
	addi s3, s6, 16
	lbu t3, 0(s6)
	sb t3, 16(s6)
	lbu t3, 1(s6)
	sb t3, 17(s6)
	lbu t3, 2(s6)
	sb t3, 18(s6)
	lbu t3, 3(s6)
	sb t3, 19(s6)
	lbu t3, 4(s6)
	sb t3, 20(s6)
	lbu t3, 5(s6)
	sb t3, 21(s6)
	lbu t3, 6(s6)
	sb t3, 22(s6)
	lbu t3, 7(s6)
	sb t3, 23(s6)
	lbu t3, 8(s6)
	sb t3, 24(s6)
	lbu t3, 9(s6)
	sb t3, 25(s6)
	lbu t3, 10(s6)
	sb t3, 26(s6)
	lbu t3, 11(s6)
	sb t3, 27(s6)
	lbu t3, 12(s6)
	sb t3, 28(s6)
	lbu t3, 13(s6)
	sb t3, 29(s6)
	lbu t3, 14(s6)
	sb t3, 30(s6)
	lbu t3, 15(s6)
	sb t3, 31(s6)
	lbu t1, 0(s3)
	lbu t2, 1(s3)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s3)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s3)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t3, 4(s3)
	lbu t2, 5(s3)
	slli t2, t2, 8
	or t3, t3, t2
	lbu t2, 6(s3)
	slli t2, t2, 16
	or t3, t3, t2
	lbu t2, 7(s3)
	slli t2, t2, 24
	or t3, t3, t2
	lbu t4, 8(s3)
	lbu t2, 9(s3)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 10(s3)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 11(s3)
	slli t2, t2, 24
	or t4, t4, t2
	lbu t5, 12(s3)
	lbu t2, 13(s3)
	slli t2, t2, 8
	or t5, t5, t2
	lbu t2, 14(s3)
	slli t2, t2, 16
	or t5, t5, t2
	lbu t2, 15(s3)
	slli t2, t2, 24
	or t5, t5, t2
	srli t6, t5, 31
	addi t2, zero, 0
	sub t6, t2, t6
	addi t2, zero, 135
	and t6, t6, t2
	slli a6, t1, 1
	xor a6, a6, t6
	sb a6, 0(s3)
	srli t2, a6, 8
	sb t2, 1(s3)
	srli t2, a6, 16
	sb t2, 2(s3)
	srli t2, a6, 24
	sb t2, 3(s3)
	slli a6, t3, 1
	srli t6, t1, 31
	or a6, a6, t6
	sb a6, 4(s3)
	srli t2, a6, 8
	sb t2, 5(s3)
	srli t2, a6, 16
	sb t2, 6(s3)
	srli t2, a6, 24
	sb t2, 7(s3)
	slli a6, t4, 1
	srli t6, t3, 31
	or a6, a6, t6
	sb a6, 8(s3)
	srli t2, a6, 8
	sb t2, 9(s3)
	srli t2, a6, 16
	sb t2, 10(s3)
	srli t2, a6, 24
	sb t2, 11(s3)
	slli a6, t5, 1
	srli t6, t4, 31
	or a6, a6, t6
	sb a6, 12(s3)
	srli t2, a6, 8
	sb t2, 13(s3)
	srli t2, a6, 16
	sb t2, 14(s3)
	srli t2, a6, 24
	sb t2, 15(s3)
	srli t1, s5, 4
	slli t1, t1, 4
	sub t2, s5, t1
	add a3, s4, t1
	addi a3, a3, -16
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 16
	addi a4, zero, 1
	addi a5, s6, 96
	call {vg_aes_xts_decrypt}
	srli t1, s5, 4
	slli t1, t1, 4
	sub t2, s5, t1
	add t3, s4, t1
	addi t3, t3, -16
22:
	lbu t4, 0(t3)
	lbu t5, 16(t3)
	sb t5, 0(t3)
	sb t4, 16(t3)
	addi t3, t3, 1
	addi t2, t2, -1
	bnez t2, 22b
	add a3, s4, t1
	addi a3, a3, -16
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 0
	addi a4, zero, 1
	addi a5, s6, 96
	call {vg_aes_xts_decrypt}
	j 21f
20:
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s6, 0
	addi a3, s4, 0
	srli a4, s5, 4
	addi a5, s6, 96
	call {vg_aes_xts_decrypt}
21:
	addi t0, s6, 39
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	ret
	.option pop
