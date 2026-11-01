// The functions of `src/internal/vg_rc2_cbc_encrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt:
	.option push
	.option arch, +m, +c
	sd s1, 256(a4)
	sd s2, 264(a4)
	sd s3, 272(a4)
	sd s4, 280(a4)
	sd s6, 296(a4)
	sd ra, 304(a4)
	sd s5, 288(a4)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi s5, a4, 0
	beqz s4, 20f
22:
	lbu t0, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	lbu t2, 0(s2)
	lbu a7, 1(s2)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 2(s2)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 3(s2)
	slli a7, a7, 24
	or t2, t2, a7
	lbu t1, 4(s2)
	lbu a7, 5(s2)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s2)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s2)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t2, t2, t1
	xor t0, t0, t2
	sb t0, 0(s3)
	srli a7, t0, 8
	sb a7, 1(s3)
	srli a7, t0, 16
	sb a7, 2(s3)
	srli a7, t0, 24
	sb a7, 3(s3)
	srli t1, t0, 32
	sb t1, 4(s3)
	srli a7, t1, 8
	sb a7, 5(s3)
	srli a7, t1, 16
	sb a7, 6(s3)
	srli a7, t1, 24
	sb a7, 7(s3)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s5, 0
	call {vg_rc2_encrypt_block}
	lbu t0, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	sb t0, 0(s2)
	srli a7, t0, 8
	sb a7, 1(s2)
	srli a7, t0, 16
	sb a7, 2(s2)
	srli a7, t0, 24
	sb a7, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli a7, t1, 8
	sb a7, 5(s2)
	srli a7, t1, 16
	sb a7, 6(s2)
	srli a7, t1, 24
	sb a7, 7(s2)
	addi s3, s3, 8
	addi s4, s4, -1
	bnez s4, 22b
	j 21f
20:
21:
	ld s1, 256(s5)
	ld s2, 264(s5)
	ld s3, 272(s5)
	ld s4, 280(s5)
	ld s6, 296(s5)
	ld ra, 304(s5)
	ld s5, 288(s5)
	ret
	.option pop
