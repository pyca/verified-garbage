// The functions of `src/internal/vg_ed448_scalar_reduce.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_reduce:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi t3, a1, 0
	addi a4, zero, 0
	sw a4, 0(a3)
	sw a4, 4(a3)
	sw a4, 8(a3)
	sw a4, 12(a3)
	sw a4, 16(a3)
	sw a4, 20(a3)
	sw a4, 24(a3)
	sw a4, 28(a3)
	sw a4, 32(a3)
	sw a4, 36(a3)
	sw a4, 40(a3)
	sw a4, 44(a3)
	sw a4, 48(a3)
	sw a4, 52(a3)
	addi t4, zero, 114
20:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 57
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 58
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 59
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 60
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 61
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 62
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	slli a5, t5, 63
	srli a5, a5, 63
	lwu a4, 0(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 0(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 4(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 8(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 12(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 16(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 20(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 24(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 28(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 0(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 4(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 8(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 12(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 16(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 20(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 24(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 28(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 32(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	lui a2, 786432
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 108(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 0(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 0(a3)
	sw a4, 56(a3)
	lwu a2, 4(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 4(a3)
	sw a4, 60(a3)
	lwu a2, 8(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 8(a3)
	sw a4, 64(a3)
	lwu a2, 12(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 12(a3)
	sw a4, 68(a3)
	lwu a2, 16(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 16(a3)
	sw a4, 72(a3)
	lwu a2, 20(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 20(a3)
	sw a4, 76(a3)
	lwu a2, 24(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 24(a3)
	sw a4, 80(a3)
	lwu a2, 28(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 28(a3)
	sw a4, 84(a3)
	lwu a2, 32(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 32(a3)
	sw a4, 88(a3)
	lwu a2, 36(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 36(a3)
	sw a4, 92(a3)
	lwu a2, 40(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 40(a3)
	sw a4, 96(a3)
	lwu a2, 44(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 44(a3)
	sw a4, 100(a3)
	lwu a2, 48(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 48(a3)
	sw a4, 104(a3)
	lwu a2, 52(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 52(a3)
	sw a4, 108(a3)
	bnez t4, 20b
	lwu a4, 0(a3)
	sb a4, 0(a0)
	srli a5, a4, 8
	sb a5, 1(a0)
	srli a5, a4, 16
	sb a5, 2(a0)
	srli a5, a4, 24
	sb a5, 3(a0)
	lwu a4, 4(a3)
	sb a4, 4(a0)
	srli a5, a4, 8
	sb a5, 5(a0)
	srli a5, a4, 16
	sb a5, 6(a0)
	srli a5, a4, 24
	sb a5, 7(a0)
	lwu a4, 8(a3)
	sb a4, 8(a0)
	srli a5, a4, 8
	sb a5, 9(a0)
	srli a5, a4, 16
	sb a5, 10(a0)
	srli a5, a4, 24
	sb a5, 11(a0)
	lwu a4, 12(a3)
	sb a4, 12(a0)
	srli a5, a4, 8
	sb a5, 13(a0)
	srli a5, a4, 16
	sb a5, 14(a0)
	srli a5, a4, 24
	sb a5, 15(a0)
	lwu a4, 16(a3)
	sb a4, 16(a0)
	srli a5, a4, 8
	sb a5, 17(a0)
	srli a5, a4, 16
	sb a5, 18(a0)
	srli a5, a4, 24
	sb a5, 19(a0)
	lwu a4, 20(a3)
	sb a4, 20(a0)
	srli a5, a4, 8
	sb a5, 21(a0)
	srli a5, a4, 16
	sb a5, 22(a0)
	srli a5, a4, 24
	sb a5, 23(a0)
	lwu a4, 24(a3)
	sb a4, 24(a0)
	srli a5, a4, 8
	sb a5, 25(a0)
	srli a5, a4, 16
	sb a5, 26(a0)
	srli a5, a4, 24
	sb a5, 27(a0)
	lwu a4, 28(a3)
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	lwu a4, 32(a3)
	sb a4, 32(a0)
	srli a5, a4, 8
	sb a5, 33(a0)
	srli a5, a4, 16
	sb a5, 34(a0)
	srli a5, a4, 24
	sb a5, 35(a0)
	lwu a4, 36(a3)
	sb a4, 36(a0)
	srli a5, a4, 8
	sb a5, 37(a0)
	srli a5, a4, 16
	sb a5, 38(a0)
	srli a5, a4, 24
	sb a5, 39(a0)
	lwu a4, 40(a3)
	sb a4, 40(a0)
	srli a5, a4, 8
	sb a5, 41(a0)
	srli a5, a4, 16
	sb a5, 42(a0)
	srli a5, a4, 24
	sb a5, 43(a0)
	lwu a4, 44(a3)
	sb a4, 44(a0)
	srli a5, a4, 8
	sb a5, 45(a0)
	srli a5, a4, 16
	sb a5, 46(a0)
	srli a5, a4, 24
	sb a5, 47(a0)
	lwu a4, 48(a3)
	sb a4, 48(a0)
	srli a5, a4, 8
	sb a5, 49(a0)
	srli a5, a4, 16
	sb a5, 50(a0)
	srli a5, a4, 24
	sb a5, 51(a0)
	lwu a4, 52(a3)
	sb a4, 52(a0)
	srli a5, a4, 8
	sb a5, 53(a0)
	srli a5, a4, 16
	sb a5, 54(a0)
	srli a5, a4, 24
	sb a5, 55(a0)
	addi a4, zero, 0
	sb a4, 56(a0)
	ret
	.option pop
