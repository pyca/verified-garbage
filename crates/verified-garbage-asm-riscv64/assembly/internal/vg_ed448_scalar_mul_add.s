// The functions of `src/internal/vg_ed448_scalar_mul_add.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_mul_add:
	.option push
	.option arch, +m, +c
	addi t6, a3, 0
	addi t2, a1, 0
	addi t3, a2, 0
	addi a3, a4, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi a4, zero, 0
	sw a4, 112(a3)
	sw a4, 116(a3)
	sw a4, 120(a3)
	sw a4, 124(a3)
	sw a4, 128(a3)
	sw a4, 132(a3)
	sw a4, 136(a3)
	sw a4, 140(a3)
	sw a4, 144(a3)
	sw a4, 148(a3)
	sw a4, 152(a3)
	sw a4, 156(a3)
	sw a4, 160(a3)
	sw a4, 164(a3)
	addi t4, zero, 57
20:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 57
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 58
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 59
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 60
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 61
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 62
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	slli a5, t5, 63
	srli a5, a5, 63
	lwu a4, 112(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 112(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 116(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 120(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 124(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 128(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 132(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 136(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 140(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 144(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 148(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 152(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 156(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 112(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 116(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 120(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 124(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 128(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 132(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 136(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 140(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 144(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 148(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 152(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 156(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 160(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
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
	lwu a2, 112(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 56(a3)
	lwu a2, 116(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 60(a3)
	lwu a2, 120(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 64(a3)
	lwu a2, 124(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 68(a3)
	lwu a2, 128(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 72(a3)
	lwu a2, 132(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 76(a3)
	lwu a2, 136(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 80(a3)
	lwu a2, 140(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 84(a3)
	lwu a2, 144(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 88(a3)
	lwu a2, 148(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 92(a3)
	lwu a2, 152(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 96(a3)
	lwu a2, 156(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 100(a3)
	lwu a2, 160(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 104(a3)
	lwu a2, 164(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 108(a3)
	bnez t4, 20b
	addi t3, t6, 0
	addi a4, zero, 0
	sw a4, 168(a3)
	sw a4, 172(a3)
	sw a4, 176(a3)
	sw a4, 180(a3)
	sw a4, 184(a3)
	sw a4, 188(a3)
	sw a4, 192(a3)
	sw a4, 196(a3)
	sw a4, 200(a3)
	sw a4, 204(a3)
	sw a4, 208(a3)
	sw a4, 212(a3)
	sw a4, 216(a3)
	sw a4, 220(a3)
	addi t4, zero, 57
21:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 57
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 58
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 59
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 60
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 61
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 62
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	slli a5, t5, 63
	srli a5, a5, 63
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 168(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 192(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 196(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 200(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 204(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 208(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 212(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 216(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 220(a3)
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
	lwu a2, 168(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 56(a3)
	lwu a2, 172(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 60(a3)
	lwu a2, 176(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 64(a3)
	lwu a2, 180(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 68(a3)
	lwu a2, 184(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 72(a3)
	lwu a2, 188(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 76(a3)
	lwu a2, 192(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 192(a3)
	sw a4, 80(a3)
	lwu a2, 196(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 196(a3)
	sw a4, 84(a3)
	lwu a2, 200(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 200(a3)
	sw a4, 88(a3)
	lwu a2, 204(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 204(a3)
	sw a4, 92(a3)
	lwu a2, 208(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 208(a3)
	sw a4, 96(a3)
	lwu a2, 212(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 212(a3)
	sw a4, 100(a3)
	lwu a2, 216(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 216(a3)
	sw a4, 104(a3)
	lwu a2, 220(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 220(a3)
	sw a4, 108(a3)
	bnez t4, 21b
	addi t3, t2, 0
	addi a4, zero, 0
	sw a4, 224(a3)
	sw a4, 228(a3)
	sw a4, 232(a3)
	sw a4, 236(a3)
	sw a4, 240(a3)
	sw a4, 244(a3)
	sw a4, 248(a3)
	sw a4, 252(a3)
	sw a4, 256(a3)
	sw a4, 260(a3)
	sw a4, 264(a3)
	sw a4, 268(a3)
	sw a4, 272(a3)
	sw a4, 276(a3)
	addi t4, zero, 57
22:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 57
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 58
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 59
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 60
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 61
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 62
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	slli a5, t5, 63
	srli a5, a5, 63
	lwu a4, 224(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 224(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 228(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 232(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 236(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 240(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 244(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 248(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 252(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 256(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 260(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 264(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 268(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 272(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 276(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 224(a3)
	lui a2, 346748
	addiw a2, a2, -1268
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 228(a3)
	lui a2, 903284
	addiw a2, a2, -659
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	lwu a4, 232(a3)
	lui a2, 467879
	addiw a2, a2, 170
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 64(a3)
	srli a5, a4, 32
	lwu a4, 236(a3)
	lui a2, 911668
	addiw a2, a2, -627
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 68(a3)
	srli a5, a4, 32
	lwu a4, 240(a3)
	lui a2, 332445
	addiw a2, a2, -1681
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 72(a3)
	srli a5, a4, 32
	lwu a4, 244(a3)
	lui a2, 244498
	addiw a2, a2, 1206
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 76(a3)
	srli a5, a4, 32
	lwu a4, 248(a3)
	lui a2, 537438
	addiw a2, a2, -1002
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 80(a3)
	srli a5, a4, 32
	lwu a4, 252(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 84(a3)
	srli a5, a4, 32
	lwu a4, 256(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 88(a3)
	srli a5, a4, 32
	lwu a4, 260(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 92(a3)
	srli a5, a4, 32
	lwu a4, 264(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 96(a3)
	srli a5, a4, 32
	lwu a4, 268(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 100(a3)
	srli a5, a4, 32
	lwu a4, 272(a3)
	lui a2, 0
	addiw a2, a2, 0
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 104(a3)
	srli a5, a4, 32
	lwu a4, 276(a3)
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
	lwu a2, 224(a3)
	lwu a4, 56(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 224(a3)
	sw a4, 56(a3)
	lwu a2, 228(a3)
	lwu a4, 60(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 228(a3)
	sw a4, 60(a3)
	lwu a2, 232(a3)
	lwu a4, 64(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 232(a3)
	sw a4, 64(a3)
	lwu a2, 236(a3)
	lwu a4, 68(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 236(a3)
	sw a4, 68(a3)
	lwu a2, 240(a3)
	lwu a4, 72(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 240(a3)
	sw a4, 72(a3)
	lwu a2, 244(a3)
	lwu a4, 76(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 244(a3)
	sw a4, 76(a3)
	lwu a2, 248(a3)
	lwu a4, 80(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 248(a3)
	sw a4, 80(a3)
	lwu a2, 252(a3)
	lwu a4, 84(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 252(a3)
	sw a4, 84(a3)
	lwu a2, 256(a3)
	lwu a4, 88(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 256(a3)
	sw a4, 88(a3)
	lwu a2, 260(a3)
	lwu a4, 92(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 260(a3)
	sw a4, 92(a3)
	lwu a2, 264(a3)
	lwu a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 264(a3)
	sw a4, 96(a3)
	lwu a2, 268(a3)
	lwu a4, 100(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 268(a3)
	sw a4, 100(a3)
	lwu a2, 272(a3)
	lwu a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 272(a3)
	sw a4, 104(a3)
	lwu a2, 276(a3)
	lwu a4, 108(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 276(a3)
	sw a4, 108(a3)
	bnez t4, 22b
	addi a4, zero, 0
	sw a4, 952(a3)
	sw a4, 956(a3)
	sw a4, 960(a3)
	sw a4, 964(a3)
	sw a4, 968(a3)
	sw a4, 972(a3)
	sw a4, 976(a3)
	sw a4, 980(a3)
	sw a4, 984(a3)
	sw a4, 988(a3)
	sw a4, 992(a3)
	sw a4, 996(a3)
	sw a4, 1000(a3)
	sw a4, 1004(a3)
	addi a6, a3, 0
	addi t0, zero, 14
23:
	lwu a1, 112(a6)
	addi a5, zero, 0
	lwu a2, 168(a3)
	mul a2, a1, a2
	lwu a4, 952(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 952(a6)
	srli a5, a4, 32
	lwu a2, 172(a3)
	mul a2, a1, a2
	lwu a4, 956(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 956(a6)
	srli a5, a4, 32
	lwu a2, 176(a3)
	mul a2, a1, a2
	lwu a4, 960(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 960(a6)
	srli a5, a4, 32
	lwu a2, 180(a3)
	mul a2, a1, a2
	lwu a4, 964(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 964(a6)
	srli a5, a4, 32
	lwu a2, 184(a3)
	mul a2, a1, a2
	lwu a4, 968(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 968(a6)
	srli a5, a4, 32
	lwu a2, 188(a3)
	mul a2, a1, a2
	lwu a4, 972(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 972(a6)
	srli a5, a4, 32
	lwu a2, 192(a3)
	mul a2, a1, a2
	lwu a4, 976(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 976(a6)
	srli a5, a4, 32
	lwu a2, 196(a3)
	mul a2, a1, a2
	lwu a4, 980(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 980(a6)
	srli a5, a4, 32
	lwu a2, 200(a3)
	mul a2, a1, a2
	lwu a4, 984(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 984(a6)
	srli a5, a4, 32
	lwu a2, 204(a3)
	mul a2, a1, a2
	lwu a4, 988(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 988(a6)
	srli a5, a4, 32
	lwu a2, 208(a3)
	mul a2, a1, a2
	lwu a4, 992(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 992(a6)
	srli a5, a4, 32
	lwu a2, 212(a3)
	mul a2, a1, a2
	lwu a4, 996(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 996(a6)
	srli a5, a4, 32
	lwu a2, 216(a3)
	mul a2, a1, a2
	lwu a4, 1000(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 1000(a6)
	srli a5, a4, 32
	lwu a2, 220(a3)
	mul a2, a1, a2
	lwu a4, 1004(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 1004(a6)
	srli a5, a4, 32
	sw a5, 1008(a6)
	addi a6, a6, 4
	addi t0, t0, -1
	bnez t0, 23b
	addi a5, zero, 0
	lwu a4, 952(a3)
	lwu a2, 224(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 952(a3)
	srli a5, a4, 32
	lwu a4, 956(a3)
	lwu a2, 228(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 956(a3)
	srli a5, a4, 32
	lwu a4, 960(a3)
	lwu a2, 232(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 960(a3)
	srli a5, a4, 32
	lwu a4, 964(a3)
	lwu a2, 236(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 964(a3)
	srli a5, a4, 32
	lwu a4, 968(a3)
	lwu a2, 240(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 968(a3)
	srli a5, a4, 32
	lwu a4, 972(a3)
	lwu a2, 244(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 972(a3)
	srli a5, a4, 32
	lwu a4, 976(a3)
	lwu a2, 248(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 976(a3)
	srli a5, a4, 32
	lwu a4, 980(a3)
	lwu a2, 252(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 980(a3)
	srli a5, a4, 32
	lwu a4, 984(a3)
	lwu a2, 256(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 984(a3)
	srli a5, a4, 32
	lwu a4, 988(a3)
	lwu a2, 260(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 988(a3)
	srli a5, a4, 32
	lwu a4, 992(a3)
	lwu a2, 264(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 992(a3)
	srli a5, a4, 32
	lwu a4, 996(a3)
	lwu a2, 268(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 996(a3)
	srli a5, a4, 32
	lwu a4, 1000(a3)
	lwu a2, 272(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 1000(a3)
	srli a5, a4, 32
	lwu a4, 1004(a3)
	lwu a2, 276(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 1004(a3)
	srli a5, a4, 32
	lwu a4, 1008(a3)
	add a4, a4, a5
	sw a4, 1008(a3)
	srli a5, a4, 32
	lwu a4, 1012(a3)
	add a4, a4, a5
	sw a4, 1012(a3)
	srli a5, a4, 32
	lwu a4, 1016(a3)
	add a4, a4, a5
	sw a4, 1016(a3)
	srli a5, a4, 32
	lwu a4, 1020(a3)
	add a4, a4, a5
	sw a4, 1020(a3)
	srli a5, a4, 32
	lwu a4, 1024(a3)
	add a4, a4, a5
	sw a4, 1024(a3)
	srli a5, a4, 32
	lwu a4, 1028(a3)
	add a4, a4, a5
	sw a4, 1028(a3)
	srli a5, a4, 32
	lwu a4, 1032(a3)
	add a4, a4, a5
	sw a4, 1032(a3)
	srli a5, a4, 32
	lwu a4, 1036(a3)
	add a4, a4, a5
	sw a4, 1036(a3)
	srli a5, a4, 32
	lwu a4, 1040(a3)
	add a4, a4, a5
	sw a4, 1040(a3)
	srli a5, a4, 32
	lwu a4, 1044(a3)
	add a4, a4, a5
	sw a4, 1044(a3)
	srli a5, a4, 32
	lwu a4, 1048(a3)
	add a4, a4, a5
	sw a4, 1048(a3)
	srli a5, a4, 32
	lwu a4, 1052(a3)
	add a4, a4, a5
	sw a4, 1052(a3)
	srli a5, a4, 32
	lwu a4, 1056(a3)
	add a4, a4, a5
	sw a4, 1056(a3)
	srli a5, a4, 32
	lwu a4, 1060(a3)
	add a4, a4, a5
	sw a4, 1060(a3)
	srli a5, a4, 32
	addi t3, a3, 280
	lwu a4, 952(a3)
	sw a4, 0(t3)
	lwu a4, 956(a3)
	sw a4, 4(t3)
	lwu a4, 960(a3)
	sw a4, 8(t3)
	lwu a4, 964(a3)
	sw a4, 12(t3)
	lwu a4, 968(a3)
	sw a4, 16(t3)
	lwu a4, 972(a3)
	sw a4, 20(t3)
	lwu a4, 976(a3)
	sw a4, 24(t3)
	lwu a4, 980(a3)
	sw a4, 28(t3)
	lwu a4, 984(a3)
	sw a4, 32(t3)
	lwu a4, 988(a3)
	sw a4, 36(t3)
	lwu a4, 992(a3)
	sw a4, 40(t3)
	lwu a4, 996(a3)
	sw a4, 44(t3)
	lwu a4, 1000(a3)
	sw a4, 48(t3)
	lwu a4, 1004(a3)
	sw a4, 52(t3)
	lwu a4, 1008(a3)
	sw a4, 56(t3)
	lwu a4, 1012(a3)
	sw a4, 60(t3)
	lwu a4, 1016(a3)
	sw a4, 64(t3)
	lwu a4, 1020(a3)
	sw a4, 68(t3)
	lwu a4, 1024(a3)
	sw a4, 72(t3)
	lwu a4, 1028(a3)
	sw a4, 76(t3)
	lwu a4, 1032(a3)
	sw a4, 80(t3)
	lwu a4, 1036(a3)
	sw a4, 84(t3)
	lwu a4, 1040(a3)
	sw a4, 88(t3)
	lwu a4, 1044(a3)
	sw a4, 92(t3)
	lwu a4, 1048(a3)
	sw a4, 96(t3)
	lwu a4, 1052(a3)
	sw a4, 100(t3)
	lwu a4, 1056(a3)
	sw a4, 104(t3)
	lwu a4, 1060(a3)
	sw a4, 108(t3)
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
	addi t4, zero, 112
24:
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
	bnez t4, 24b
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
