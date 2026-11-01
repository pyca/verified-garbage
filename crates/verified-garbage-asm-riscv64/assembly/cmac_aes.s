// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys:
	.option push
	.option arch, +m, +c
	addi t0, a3, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd ra, 16(t0)
	sd s1, 24(t0)
	sd s2, 32(t0)
	addi s1, a2, 0
	addi s2, a3, 0
	addi t1, zero, 0
	sb t1, 0(s1)
	addi t1, zero, 0
	sb t1, 1(s1)
	addi t1, zero, 0
	sb t1, 2(s1)
	addi t1, zero, 0
	sb t1, 3(s1)
	addi t1, zero, 0
	sb t1, 4(s1)
	addi t1, zero, 0
	sb t1, 5(s1)
	addi t1, zero, 0
	sb t1, 6(s1)
	addi t1, zero, 0
	sb t1, 7(s1)
	addi t1, zero, 0
	sb t1, 8(s1)
	addi t1, zero, 0
	sb t1, 9(s1)
	addi t1, zero, 0
	sb t1, 10(s1)
	addi t1, zero, 0
	sb t1, 11(s1)
	addi t1, zero, 0
	sb t1, 12(s1)
	addi t1, zero, 0
	sb t1, 13(s1)
	addi t1, zero, 0
	sb t1, 14(s1)
	addi t1, zero, 0
	sb t1, 15(s1)
	addi a2, s1, 0
	addi a3, zero, 1
	addi a4, s2, 0
	call {vg_aes_encrypt_blocks}
	lbu t1, 0(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 1(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 0(s1)
	addi t1, t3, 0
	lbu t3, 2(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 1(s1)
	addi t1, t3, 0
	lbu t3, 3(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 2(s1)
	addi t1, t3, 0
	lbu t3, 4(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 3(s1)
	addi t1, t3, 0
	lbu t3, 5(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 4(s1)
	addi t1, t3, 0
	lbu t3, 6(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 5(s1)
	addi t1, t3, 0
	lbu t3, 7(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 6(s1)
	addi t1, t3, 0
	lbu t3, 8(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 7(s1)
	addi t1, t3, 0
	lbu t3, 9(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 8(s1)
	addi t1, t3, 0
	lbu t3, 10(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 9(s1)
	addi t1, t3, 0
	lbu t3, 11(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 10(s1)
	addi t1, t3, 0
	lbu t3, 12(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 11(s1)
	addi t1, t3, 0
	lbu t3, 13(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 12(s1)
	addi t1, t3, 0
	lbu t3, 14(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 13(s1)
	addi t1, t3, 0
	lbu t3, 15(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 14(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 15(s1)
	lbu t1, 0(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 1(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 16(s1)
	addi t1, t3, 0
	lbu t3, 2(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 17(s1)
	addi t1, t3, 0
	lbu t3, 3(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 18(s1)
	addi t1, t3, 0
	lbu t3, 4(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 19(s1)
	addi t1, t3, 0
	lbu t3, 5(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 20(s1)
	addi t1, t3, 0
	lbu t3, 6(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 21(s1)
	addi t1, t3, 0
	lbu t3, 7(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 22(s1)
	addi t1, t3, 0
	lbu t3, 8(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 23(s1)
	addi t1, t3, 0
	lbu t3, 9(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 24(s1)
	addi t1, t3, 0
	lbu t3, 10(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 25(s1)
	addi t1, t3, 0
	lbu t3, 11(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 26(s1)
	addi t1, t3, 0
	lbu t3, 12(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 27(s1)
	addi t1, t3, 0
	lbu t3, 13(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 28(s1)
	addi t1, t3, 0
	lbu t3, 14(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 29(s1)
	addi t1, t3, 0
	lbu t3, 15(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 30(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 31(s1)
	addi t0, s2, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s1, 24(t0)
	ld s2, 32(t0)
	ret
	.option pop

vg_cmac_aes_update:
	.option push
	.option arch, +m, +c
	addi t0, a5, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd ra, 16(t0)
	sd s1, 24(t0)
	sd s2, 32(t0)
	sd s3, 40(t0)
	sd s4, 48(t0)
	sd s5, 56(t0)
	sd s6, 64(t0)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi s5, a4, 0
	addi s6, a5, 0
	beqz s5, 20f
22:
	lbu t3, 0(s3)
	lbu t4, 0(s4)
	xor t3, t3, t4
	sb t3, 0(s3)
	lbu t3, 1(s3)
	lbu t4, 1(s4)
	xor t3, t3, t4
	sb t3, 1(s3)
	lbu t3, 2(s3)
	lbu t4, 2(s4)
	xor t3, t3, t4
	sb t3, 2(s3)
	lbu t3, 3(s3)
	lbu t4, 3(s4)
	xor t3, t3, t4
	sb t3, 3(s3)
	lbu t3, 4(s3)
	lbu t4, 4(s4)
	xor t3, t3, t4
	sb t3, 4(s3)
	lbu t3, 5(s3)
	lbu t4, 5(s4)
	xor t3, t3, t4
	sb t3, 5(s3)
	lbu t3, 6(s3)
	lbu t4, 6(s4)
	xor t3, t3, t4
	sb t3, 6(s3)
	lbu t3, 7(s3)
	lbu t4, 7(s4)
	xor t3, t3, t4
	sb t3, 7(s3)
	lbu t3, 8(s3)
	lbu t4, 8(s4)
	xor t3, t3, t4
	sb t3, 8(s3)
	lbu t3, 9(s3)
	lbu t4, 9(s4)
	xor t3, t3, t4
	sb t3, 9(s3)
	lbu t3, 10(s3)
	lbu t4, 10(s4)
	xor t3, t3, t4
	sb t3, 10(s3)
	lbu t3, 11(s3)
	lbu t4, 11(s4)
	xor t3, t3, t4
	sb t3, 11(s3)
	lbu t3, 12(s3)
	lbu t4, 12(s4)
	xor t3, t3, t4
	sb t3, 12(s3)
	lbu t3, 13(s3)
	lbu t4, 13(s4)
	xor t3, t3, t4
	sb t3, 13(s3)
	lbu t3, 14(s3)
	lbu t4, 14(s4)
	xor t3, t3, t4
	sb t3, 14(s3)
	lbu t3, 15(s3)
	lbu t4, 15(s4)
	xor t3, t3, t4
	sb t3, 15(s3)
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s3, 0
	addi a3, zero, 1
	addi a4, s6, 0
	call {vg_aes_encrypt_blocks}
	addi s4, s4, 16
	addi s5, s5, -1
	bnez s5, 22b
	j 21f
20:
21:
	addi t0, s6, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s1, 24(t0)
	ld s2, 32(t0)
	ld s3, 40(t0)
	ld s4, 48(t0)
	ld s5, 56(t0)
	ld s6, 64(t0)
	ret
	.option pop

vg_cmac_aes_finalize:
	.option push
	.option arch, +m, +c
	addi t0, a5, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd ra, 16(t0)
	sd s1, 24(t0)
	addi s1, a5, 0
	addi t1, a4, -16
	beqz t1, 20f
	addi t5, a3, 0
	addi t6, a2, 0
	addi t1, a4, 0
	beqz t1, 22f
24:
	lbu t3, 0(t5)
	lbu t4, 0(t6)
	xor t3, t3, t4
	sb t3, 0(t6)
	addi t5, t5, 1
	addi t6, t6, 1
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
23:
	lbu t3, 0(t6)
	xori t3, t3, 128
	sb t3, 0(t6)
	addi t5, a0, 256
	lbu t3, 0(a2)
	lbu t4, 0(t5)
	xor t3, t3, t4
	sb t3, 0(a2)
	lbu t3, 1(a2)
	lbu t4, 1(t5)
	xor t3, t3, t4
	sb t3, 1(a2)
	lbu t3, 2(a2)
	lbu t4, 2(t5)
	xor t3, t3, t4
	sb t3, 2(a2)
	lbu t3, 3(a2)
	lbu t4, 3(t5)
	xor t3, t3, t4
	sb t3, 3(a2)
	lbu t3, 4(a2)
	lbu t4, 4(t5)
	xor t3, t3, t4
	sb t3, 4(a2)
	lbu t3, 5(a2)
	lbu t4, 5(t5)
	xor t3, t3, t4
	sb t3, 5(a2)
	lbu t3, 6(a2)
	lbu t4, 6(t5)
	xor t3, t3, t4
	sb t3, 6(a2)
	lbu t3, 7(a2)
	lbu t4, 7(t5)
	xor t3, t3, t4
	sb t3, 7(a2)
	lbu t3, 8(a2)
	lbu t4, 8(t5)
	xor t3, t3, t4
	sb t3, 8(a2)
	lbu t3, 9(a2)
	lbu t4, 9(t5)
	xor t3, t3, t4
	sb t3, 9(a2)
	lbu t3, 10(a2)
	lbu t4, 10(t5)
	xor t3, t3, t4
	sb t3, 10(a2)
	lbu t3, 11(a2)
	lbu t4, 11(t5)
	xor t3, t3, t4
	sb t3, 11(a2)
	lbu t3, 12(a2)
	lbu t4, 12(t5)
	xor t3, t3, t4
	sb t3, 12(a2)
	lbu t3, 13(a2)
	lbu t4, 13(t5)
	xor t3, t3, t4
	sb t3, 13(a2)
	lbu t3, 14(a2)
	lbu t4, 14(t5)
	xor t3, t3, t4
	sb t3, 14(a2)
	lbu t3, 15(a2)
	lbu t4, 15(t5)
	xor t3, t3, t4
	sb t3, 15(a2)
	j 21f
20:
	lbu t3, 0(a2)
	lbu t4, 0(a3)
	xor t3, t3, t4
	sb t3, 0(a2)
	lbu t3, 1(a2)
	lbu t4, 1(a3)
	xor t3, t3, t4
	sb t3, 1(a2)
	lbu t3, 2(a2)
	lbu t4, 2(a3)
	xor t3, t3, t4
	sb t3, 2(a2)
	lbu t3, 3(a2)
	lbu t4, 3(a3)
	xor t3, t3, t4
	sb t3, 3(a2)
	lbu t3, 4(a2)
	lbu t4, 4(a3)
	xor t3, t3, t4
	sb t3, 4(a2)
	lbu t3, 5(a2)
	lbu t4, 5(a3)
	xor t3, t3, t4
	sb t3, 5(a2)
	lbu t3, 6(a2)
	lbu t4, 6(a3)
	xor t3, t3, t4
	sb t3, 6(a2)
	lbu t3, 7(a2)
	lbu t4, 7(a3)
	xor t3, t3, t4
	sb t3, 7(a2)
	lbu t3, 8(a2)
	lbu t4, 8(a3)
	xor t3, t3, t4
	sb t3, 8(a2)
	lbu t3, 9(a2)
	lbu t4, 9(a3)
	xor t3, t3, t4
	sb t3, 9(a2)
	lbu t3, 10(a2)
	lbu t4, 10(a3)
	xor t3, t3, t4
	sb t3, 10(a2)
	lbu t3, 11(a2)
	lbu t4, 11(a3)
	xor t3, t3, t4
	sb t3, 11(a2)
	lbu t3, 12(a2)
	lbu t4, 12(a3)
	xor t3, t3, t4
	sb t3, 12(a2)
	lbu t3, 13(a2)
	lbu t4, 13(a3)
	xor t3, t3, t4
	sb t3, 13(a2)
	lbu t3, 14(a2)
	lbu t4, 14(a3)
	xor t3, t3, t4
	sb t3, 14(a2)
	lbu t3, 15(a2)
	lbu t4, 15(a3)
	xor t3, t3, t4
	sb t3, 15(a2)
	addi t5, a0, 240
	lbu t3, 0(a2)
	lbu t4, 0(t5)
	xor t3, t3, t4
	sb t3, 0(a2)
	lbu t3, 1(a2)
	lbu t4, 1(t5)
	xor t3, t3, t4
	sb t3, 1(a2)
	lbu t3, 2(a2)
	lbu t4, 2(t5)
	xor t3, t3, t4
	sb t3, 2(a2)
	lbu t3, 3(a2)
	lbu t4, 3(t5)
	xor t3, t3, t4
	sb t3, 3(a2)
	lbu t3, 4(a2)
	lbu t4, 4(t5)
	xor t3, t3, t4
	sb t3, 4(a2)
	lbu t3, 5(a2)
	lbu t4, 5(t5)
	xor t3, t3, t4
	sb t3, 5(a2)
	lbu t3, 6(a2)
	lbu t4, 6(t5)
	xor t3, t3, t4
	sb t3, 6(a2)
	lbu t3, 7(a2)
	lbu t4, 7(t5)
	xor t3, t3, t4
	sb t3, 7(a2)
	lbu t3, 8(a2)
	lbu t4, 8(t5)
	xor t3, t3, t4
	sb t3, 8(a2)
	lbu t3, 9(a2)
	lbu t4, 9(t5)
	xor t3, t3, t4
	sb t3, 9(a2)
	lbu t3, 10(a2)
	lbu t4, 10(t5)
	xor t3, t3, t4
	sb t3, 10(a2)
	lbu t3, 11(a2)
	lbu t4, 11(t5)
	xor t3, t3, t4
	sb t3, 11(a2)
	lbu t3, 12(a2)
	lbu t4, 12(t5)
	xor t3, t3, t4
	sb t3, 12(a2)
	lbu t3, 13(a2)
	lbu t4, 13(t5)
	xor t3, t3, t4
	sb t3, 13(a2)
	lbu t3, 14(a2)
	lbu t4, 14(t5)
	xor t3, t3, t4
	sb t3, 14(a2)
	lbu t3, 15(a2)
	lbu t4, 15(t5)
	xor t3, t3, t4
	sb t3, 15(a2)
21:
	addi a3, zero, 1
	addi a4, s1, 0
	call {vg_aes_encrypt_blocks}
	addi t0, s1, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s1, 24(t0)
	ret
	.option pop

vg_cmac_aes_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a3, sp, 0
	addi t0, a3, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	srli s3, a2, 2
	addi s3, s3, 6
	addi a0, a1, 0
	addi a1, a2, 0
	addi a2, s1, 0
	call {vg_aes_expand_key_scratch}
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a3, s2, 0
	call {vg_cmac_aes_subkeys}
	addi t1, zero, 0
	sb t1, 272(s1)
	addi t1, zero, 0
	sb t1, 273(s1)
	addi t1, zero, 0
	sb t1, 274(s1)
	addi t1, zero, 0
	sb t1, 275(s1)
	addi t1, zero, 0
	sb t1, 276(s1)
	addi t1, zero, 0
	sb t1, 277(s1)
	addi t1, zero, 0
	sb t1, 278(s1)
	addi t1, zero, 0
	sb t1, 279(s1)
	addi t1, zero, 0
	sb t1, 280(s1)
	addi t1, zero, 0
	sb t1, 281(s1)
	addi t1, zero, 0
	sb t1, 282(s1)
	addi t1, zero, 0
	sb t1, 283(s1)
	addi t1, zero, 0
	sb t1, 284(s1)
	addi t1, zero, 0
	sb t1, 285(s1)
	addi t1, zero, 0
	sb t1, 286(s1)
	addi t1, zero, 0
	sb t1, 287(s1)
	addi t0, s2, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	ret
	.option pop

vg_cmac_aes_absorb:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a5, sp, 0
	addi t0, a5, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	sd s6, 48(t0)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s6, a5, 0
	beqz a2, 20f
	addi t1, a2, -1
	andi t1, t1, 15
	addi t1, t1, 1
	j 21f
20:
	addi t1, zero, 0
21:
	srli t2, s4, 4
	beqz t2, 22f
	addi t2, zero, 16
	j 23f
22:
	addi t2, s4, 0
23:
	addi t3, zero, 16
	sub t3, t3, t1
	sltu t4, t2, t3
	beqz t4, 24f
	j 25f
24:
	addi t2, t3, 0
25:
	addi a7, t2, 0
	add t5, s1, t1
	addi t5, t5, 288
	addi t6, s3, 0
	beqz t2, 26f
28:
	lbu t3, 0(t6)
	sb t3, 0(t5)
	addi t6, t6, 1
	addi t5, t5, 1
	addi t2, t2, -1
	bnez t2, 28b
	j 27f
26:
27:
	add s3, s3, a7
	sub s4, s4, a7
	addi a4, zero, 0
	beqz s4, 29f
	addi a4, zero, 1
	j 210f
29:
210:
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s1, 272
	addi a3, s1, 288
	addi a5, s6, 0
	call {vg_cmac_aes_update}
	addi s5, zero, 0
	beqz s4, 211f
	addi s5, s4, -1
	andi t1, s5, 15
	sub s5, s5, t1
	j 212f
211:
212:
	srli a4, s5, 4
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s1, 272
	addi a3, s3, 0
	addi a5, s6, 0
	call {vg_cmac_aes_update}
	add s3, s3, s5
	sub s4, s4, s5
	addi t5, s1, 288
	addi t6, s3, 0
	addi t2, s4, 0
	beqz t2, 213f
215:
	lbu t3, 0(t6)
	sb t3, 0(t5)
	addi t6, t6, 1
	addi t5, t5, 1
	addi t2, t2, -1
	bnez t2, 215b
	j 214f
213:
214:
	addi t0, s6, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	ld s6, 48(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	ret
	.option pop

vg_cmac_aes_finish:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -272
	addi a4, sp, 0
	lbu t1, 272(a0)
	sb t1, 0(a3)
	lbu t1, 273(a0)
	sb t1, 1(a3)
	lbu t1, 274(a0)
	sb t1, 2(a3)
	lbu t1, 275(a0)
	sb t1, 3(a3)
	lbu t1, 276(a0)
	sb t1, 4(a3)
	lbu t1, 277(a0)
	sb t1, 5(a3)
	lbu t1, 278(a0)
	sb t1, 6(a3)
	lbu t1, 279(a0)
	sb t1, 7(a3)
	lbu t1, 280(a0)
	sb t1, 8(a3)
	lbu t1, 281(a0)
	sb t1, 9(a3)
	lbu t1, 282(a0)
	sb t1, 10(a3)
	lbu t1, 283(a0)
	sb t1, 11(a3)
	lbu t1, 284(a0)
	sb t1, 12(a3)
	lbu t1, 285(a0)
	sb t1, 13(a3)
	lbu t1, 286(a0)
	sb t1, 14(a3)
	lbu t1, 287(a0)
	sb t1, 15(a3)
	addi t0, a4, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	addi s1, a4, 0
	addi a5, a4, 0
	addi a4, a2, 0
	addi a2, a3, 0
	addi a3, a0, 288
	beqz a4, 20f
	addi a4, a4, -1
	andi a4, a4, 15
	addi a4, a4, 1
	j 21f
20:
21:
	call {vg_cmac_aes_finalize}
	addi t0, s1, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	addi sp, sp, 272
	addi sp, sp, 2032
	ret
	.option pop
