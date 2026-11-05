// The functions of `src/internal/vg_sha256_state_digest.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_state_digest:
	.option push
	.option arch, +m, +c
	addi a2, s1, 0
	addi a3, s3, 0
	addi s1, a0, 0
	addi s3, a1, 0
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 0(s3)
	srli t2, t1, 16
	sb t2, 1(s3)
	srli t2, t1, 8
	sb t2, 2(s3)
	srli t2, t1, 0
	sb t2, 3(s3)
	lbu t1, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 8(s3)
	srli t2, t1, 16
	sb t2, 9(s3)
	srli t2, t1, 8
	sb t2, 10(s3)
	srli t2, t1, 0
	sb t2, 11(s3)
	lbu t1, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 16(s3)
	srli t2, t1, 16
	sb t2, 17(s3)
	srli t2, t1, 8
	sb t2, 18(s3)
	srli t2, t1, 0
	sb t2, 19(s3)
	lbu t1, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	addi s1, a2, 0
	addi s3, a3, 0
	ret
	.option pop
