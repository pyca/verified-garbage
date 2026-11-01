// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	lui a6, 1
	addi a6, a6, -767
	addi a4, a2, -5
	beqz a4, 20f
	addi t1, zero, 32
22:
	lbu a5, 0(a0)
	lbu a4, 1(a0)
	slli a4, a4, 8
	add a5, a5, a4
	lbu a4, 2(a0)
	slli a4, a4, 16
	add a5, a5, a4
	lbu a4, 3(a0)
	slli a4, a4, 24
	add a5, a5, a4
	lbu a4, 4(a0)
	slli a4, a4, 32
	add a5, a5, a4
	lbu a4, 5(a0)
	slli a4, a4, 40
	add a5, a5, a4
	lbu t2, 5(a0)
	lbu a4, 6(a0)
	slli a4, a4, 8
	add t2, t2, a4
	lbu a4, 7(a0)
	slli a4, a4, 16
	add t2, t2, a4
	lbu a4, 8(a0)
	slli a4, a4, 24
	add t2, t2, a4
	lbu a4, 9(a0)
	slli a4, a4, 32
	add t2, t2, a4
	lbu a4, 10(a0)
	slli a4, a4, 40
	add t2, t2, a4
	slli a4, a5, 53
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 0(a3)
	slli a4, a5, 42
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 4(a3)
	slli a4, a5, 31
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 8(a3)
	slli a4, a5, 20
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 12(a3)
	slli a4, t2, 49
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 16(a3)
	slli a4, t2, 38
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 20(a3)
	slli a4, t2, 27
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 24(a3)
	slli a4, t2, 16
	srli a4, a4, 53
	mul a4, a4, a6
	addi a4, a4, 1024
	srli a4, a4, 11
	sw a4, 28(a3)
	addi a0, a0, 11
	addi a3, a3, 32
	addi t1, t1, -1
	bnez t1, 22b
	j 21f
20:
	addi t1, zero, 32
23:
	lbu a5, 0(a0)
	lbu a4, 1(a0)
	slli a4, a4, 8
	add a5, a5, a4
	lbu a4, 2(a0)
	slli a4, a4, 16
	add a5, a5, a4
	lbu a4, 3(a0)
	slli a4, a4, 24
	add a5, a5, a4
	lbu a4, 4(a0)
	slli a4, a4, 32
	add a5, a5, a4
	slli a4, a5, 59
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 0(a3)
	slli a4, a5, 54
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 4(a3)
	slli a4, a5, 49
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 8(a3)
	slli a4, a5, 44
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 12(a3)
	slli a4, a5, 39
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 16(a3)
	slli a4, a5, 34
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 20(a3)
	slli a4, a5, 29
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 24(a3)
	slli a4, a5, 24
	srli a4, a4, 59
	mul a4, a4, a6
	addi a4, a4, 16
	srli a4, a4, 5
	sw a4, 28(a3)
	addi a0, a0, 5
	addi a3, a3, 32
	addi t1, t1, -1
	bnez t1, 23b
21:
	ret
	.option pop
