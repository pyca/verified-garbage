// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	addi a4, a1, -5
	beqz a4, 20f
	lui a7, 64
	addi a7, a7, -256
	lui a6, 79
	addi a6, a6, -1042
	addi t1, zero, 32
22:
	addi a5, zero, 0
	addi t2, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 53
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 42
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 31
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 20
	add a5, a5, a4
	lwu a4, 16(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 49
	add t2, t2, a4
	lwu a4, 20(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 38
	add t2, t2, a4
	lwu a4, 24(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 27
	add t2, t2, a4
	lwu a4, 28(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 53
	srli a4, a4, 16
	add t2, t2, a4
	sb a5, 0(a2)
	srli a4, a5, 8
	sb a4, 1(a2)
	srli a4, a5, 16
	sb a4, 2(a2)
	srli a4, a5, 24
	sb a4, 3(a2)
	srli a4, a5, 32
	sb a4, 4(a2)
	srli a5, a5, 40
	add a5, a5, t2
	sb a5, 5(a2)
	srli a4, a5, 8
	sb a4, 6(a2)
	srli a4, a5, 16
	sb a4, 7(a2)
	srli a4, a5, 24
	sb a4, 8(a2)
	srli a4, a5, 32
	sb a4, 9(a2)
	srli a4, a5, 40
	sb a4, 10(a2)
	addi a0, a0, 32
	addi a2, a2, 11
	addi t1, t1, -1
	bnez t1, 22b
	j 21f
20:
	lui a7, 64
	addi a7, a7, -256
	lui a6, 1
	addi a6, a6, 944
	addi t1, zero, 32
23:
	addi a5, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 59
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 54
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 49
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 44
	add a5, a5, a4
	lwu a4, 16(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 39
	add a5, a5, a4
	lwu a4, 20(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 34
	add a5, a5, a4
	lwu a4, 24(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 29
	add a5, a5, a4
	lwu a4, 28(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 59
	srli a4, a4, 24
	add a5, a5, a4
	sb a5, 0(a2)
	srli a4, a5, 8
	sb a4, 1(a2)
	srli a4, a5, 16
	sb a4, 2(a2)
	srli a4, a5, 24
	sb a4, 3(a2)
	srli a4, a5, 32
	sb a4, 4(a2)
	addi a0, a0, 32
	addi a2, a2, 5
	addi t1, t1, -1
	bnez t1, 23b
21:
	ret
	.option pop
