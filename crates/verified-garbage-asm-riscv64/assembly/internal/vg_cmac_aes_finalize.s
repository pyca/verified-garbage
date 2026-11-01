// The functions of `src/internal/vg_cmac_aes_finalize.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
