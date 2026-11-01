// The functions of `src/internal/vg_cmac_aes_subkeys.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
