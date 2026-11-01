// The functions of `src/internal/vg_mlkem_compress_encode.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_compress_encode:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	addi a4, a1, -1
	beqz a4, 20f
	addi a4, a1, -4
	beqz a4, 22f
	lui a7, 64
	addi a7, a7, -64
	lui a6, 39
	addi a6, a6, 1527
	addi t1, zero, 64
24:
	addi a5, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 54
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 44
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
	srli a4, a4, 34
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 54
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
	addi a0, a0, 16
	addi a2, a2, 5
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
	lui a7, 64
	addi a7, a7, -64
	lui a6, 1
	addi a6, a6, -1576
	addi t1, zero, 128
25:
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 60
	srli a5, a4, 60
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 60
	srli a4, a4, 56
	add a5, a5, a4
	sb a5, 0(a2)
	addi a0, a0, 8
	addi a2, a2, 1
	addi t1, t1, -1
	bnez t1, 25b
23:
	j 21f
20:
	lui a7, 64
	addi a7, a7, -64
	addi a6, zero, 315
	addi t1, zero, 32
26:
	addi a5, zero, 0
	lwu a4, 0(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 63
	add a5, a5, a4
	lwu a4, 4(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 62
	add a5, a5, a4
	lwu a4, 8(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 61
	add a5, a5, a4
	lwu a4, 12(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 60
	add a5, a5, a4
	lwu a4, 16(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 59
	add a5, a5, a4
	lwu a4, 20(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 58
	add a5, a5, a4
	lwu a4, 24(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 57
	add a5, a5, a4
	lwu a4, 28(a0)
	mul a4, a4, a6
	add a4, a4, a7
	srli a4, a4, 19
	slli a4, a4, 63
	srli a4, a4, 56
	add a5, a5, a4
	sb a5, 0(a2)
	addi a0, a0, 32
	addi a2, a2, 1
	addi t1, t1, -1
	bnez t1, 26b
21:
	ret
	.option pop
