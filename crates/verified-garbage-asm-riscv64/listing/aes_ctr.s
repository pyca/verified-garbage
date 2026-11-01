// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr:
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
	lbu t1, 12(s3)
	slli t1, t1, 24
	lbu t2, 13(s3)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 14(s3)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 15(s3)
	or t1, t1, t2
	addi t2, zero, 1
	slli t2, t2, 32
	sub t2, t2, t1
	sltu t3, s5, t2
	addi t4, zero, 0
	sub t3, t4, t3
	xor t4, s5, t2
	and t4, t4, t3
	xor t2, t2, t4
	addi t0, s6, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd t2, 0(t0)
	addi a0, s1, 0
	addi a1, s2, 0
	addi a2, s3, 0
	addi a3, s4, 0
	addi a4, t2, 0
	addi a5, s6, 0
	call {vg_aes_ctr32}
	addi t0, s6, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld t1, 0(t0)
	sub s5, s5, t1
	slli t1, t1, 4
	add s4, s4, t1
	lbu t1, 12(s3)
	slli t1, t1, 24
	lbu t2, 13(s3)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 14(s3)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 15(s3)
	or t1, t1, t2
	beqz t1, 23f
	j 24f
23:
	lbu t1, 8(s3)
	slli t1, t1, 8
	lbu t2, 9(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 10(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 11(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 12(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 13(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 14(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 15(s3)
	or t1, t1, t2
	addi t2, zero, 1
	slli t2, t2, 32
	add t1, t1, t2
	srli t3, t1, 56
	sb t3, 8(s3)
	srli t3, t1, 48
	sb t3, 9(s3)
	srli t3, t1, 40
	sb t3, 10(s3)
	srli t3, t1, 32
	sb t3, 11(s3)
	srli t3, t1, 24
	sb t3, 12(s3)
	srli t3, t1, 16
	sb t3, 13(s3)
	srli t3, t1, 8
	sb t3, 14(s3)
	srli t3, t1, 0
	sb t3, 15(s3)
	sltu t3, t1, t2
	lbu t1, 0(s3)
	slli t1, t1, 8
	lbu t2, 1(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 2(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 3(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 4(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 5(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 6(s3)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 7(s3)
	or t1, t1, t2
	add t1, t1, t3
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
24:
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
