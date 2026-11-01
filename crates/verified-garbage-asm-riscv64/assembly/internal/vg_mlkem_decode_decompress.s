// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode_decompress:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	lui a6, 1
	addi a6, a6, -767
	addi a4, a2, -1
	beqz a4, 20f
	addi a4, a2, -4
	beqz a4, 22f
	addi t1, zero, 64
24:
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
	slli a4, a5, 54
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 0(a3)
	slli a4, a5, 44
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 4(a3)
	slli a4, a5, 34
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 8(a3)
	slli a4, a5, 24
	srli a4, a4, 54
	mul a4, a4, a6
	addi a4, a4, 512
	srli a4, a4, 10
	sw a4, 12(a3)
	addi a0, a0, 5
	addi a3, a3, 16
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
	addi t1, zero, 128
25:
	lbu a5, 0(a0)
	slli a4, a5, 60
	srli a4, a4, 60
	mul a4, a4, a6
	addi a4, a4, 8
	srli a4, a4, 4
	sw a4, 0(a3)
	srli a4, a5, 4
	mul a4, a4, a6
	addi a4, a4, 8
	srli a4, a4, 4
	sw a4, 4(a3)
	addi a0, a0, 1
	addi a3, a3, 8
	addi t1, t1, -1
	bnez t1, 25b
23:
	j 21f
20:
	addi t1, zero, 32
26:
	lbu a5, 0(a0)
	slli a4, a5, 63
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 0(a3)
	slli a4, a5, 62
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 4(a3)
	slli a4, a5, 61
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 8(a3)
	slli a4, a5, 60
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 12(a3)
	slli a4, a5, 59
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 16(a3)
	slli a4, a5, 58
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 20(a3)
	slli a4, a5, 57
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 24(a3)
	slli a4, a5, 56
	srli a4, a4, 63
	mul a4, a4, a6
	addi a4, a4, 1
	srli a4, a4, 1
	sw a4, 28(a3)
	addi a0, a0, 1
	addi a3, a3, 32
	addi t1, t1, -1
	bnez t1, 26b
21:
	ret
	.option pop
