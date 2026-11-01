// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt:
	.option push
	.option arch, +m, +c
	addi t0, a5, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd ra, 16(t0)
	sd s1, 24(t0)
	addi s1, a5, 0
	call {vg_aes_cbc_chain}
	addi t0, s1, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s1, 24(t0)
	ret
	.option pop

vg_aes_cbc_decrypt:
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
	addi t0, s6, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	lbu t3, 0(s4)
	sb t3, 0(t0)
	lbu t3, 1(s4)
	sb t3, 1(t0)
	lbu t3, 2(s4)
	sb t3, 2(t0)
	lbu t3, 3(s4)
	sb t3, 3(t0)
	lbu t3, 4(s4)
	sb t3, 4(t0)
	lbu t3, 5(s4)
	sb t3, 5(t0)
	lbu t3, 6(s4)
	sb t3, 6(t0)
	lbu t3, 7(s4)
	sb t3, 7(t0)
	lbu t3, 8(s4)
	sb t3, 8(t0)
	lbu t3, 9(s4)
	sb t3, 9(t0)
	lbu t3, 10(s4)
	sb t3, 10(t0)
	lbu t3, 11(s4)
	sb t3, 11(t0)
	lbu t3, 12(s4)
	sb t3, 12(t0)
	lbu t3, 13(s4)
	sb t3, 13(t0)
	lbu t3, 14(s4)
	sb t3, 14(t0)
	lbu t3, 15(s4)
	sb t3, 15(t0)
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s4, 0
	addi a3, zero, 1
	addi a4, s6, 0
	call {vg_aes_decrypt_blocks}
	lbu t3, 0(s4)
	lbu t4, 0(s3)
	xor t3, t3, t4
	sb t3, 0(s4)
	lbu t3, 1(s4)
	lbu t4, 1(s3)
	xor t3, t3, t4
	sb t3, 1(s4)
	lbu t3, 2(s4)
	lbu t4, 2(s3)
	xor t3, t3, t4
	sb t3, 2(s4)
	lbu t3, 3(s4)
	lbu t4, 3(s3)
	xor t3, t3, t4
	sb t3, 3(s4)
	lbu t3, 4(s4)
	lbu t4, 4(s3)
	xor t3, t3, t4
	sb t3, 4(s4)
	lbu t3, 5(s4)
	lbu t4, 5(s3)
	xor t3, t3, t4
	sb t3, 5(s4)
	lbu t3, 6(s4)
	lbu t4, 6(s3)
	xor t3, t3, t4
	sb t3, 6(s4)
	lbu t3, 7(s4)
	lbu t4, 7(s3)
	xor t3, t3, t4
	sb t3, 7(s4)
	lbu t3, 8(s4)
	lbu t4, 8(s3)
	xor t3, t3, t4
	sb t3, 8(s4)
	lbu t3, 9(s4)
	lbu t4, 9(s3)
	xor t3, t3, t4
	sb t3, 9(s4)
	lbu t3, 10(s4)
	lbu t4, 10(s3)
	xor t3, t3, t4
	sb t3, 10(s4)
	lbu t3, 11(s4)
	lbu t4, 11(s3)
	xor t3, t3, t4
	sb t3, 11(s4)
	lbu t3, 12(s4)
	lbu t4, 12(s3)
	xor t3, t3, t4
	sb t3, 12(s4)
	lbu t3, 13(s4)
	lbu t4, 13(s3)
	xor t3, t3, t4
	sb t3, 13(s4)
	lbu t3, 14(s4)
	lbu t4, 14(s3)
	xor t3, t3, t4
	sb t3, 14(s4)
	lbu t3, 15(s4)
	lbu t4, 15(s3)
	xor t3, t3, t4
	sb t3, 15(s4)
	addi t0, s6, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	lbu t3, 0(t0)
	sb t3, 0(s3)
	lbu t3, 1(t0)
	sb t3, 1(s3)
	lbu t3, 2(t0)
	sb t3, 2(s3)
	lbu t3, 3(t0)
	sb t3, 3(s3)
	lbu t3, 4(t0)
	sb t3, 4(s3)
	lbu t3, 5(t0)
	sb t3, 5(s3)
	lbu t3, 6(t0)
	sb t3, 6(s3)
	lbu t3, 7(t0)
	sb t3, 7(s3)
	lbu t3, 8(t0)
	sb t3, 8(s3)
	lbu t3, 9(t0)
	sb t3, 9(s3)
	lbu t3, 10(t0)
	sb t3, 10(s3)
	lbu t3, 11(t0)
	sb t3, 11(s3)
	lbu t3, 12(t0)
	sb t3, 12(s3)
	lbu t3, 13(t0)
	sb t3, 13(s3)
	lbu t3, 14(t0)
	sb t3, 14(s3)
	lbu t3, 15(t0)
	sb t3, 15(s3)
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
