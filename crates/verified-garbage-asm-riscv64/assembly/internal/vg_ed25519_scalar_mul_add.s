// The functions of `src/internal/vg_ed25519_scalar_mul_add.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	.option push
	.option arch, +m, +c
	addi t5, a3, 0
	addi a3, a4, 0
	addi a3, a3, 7
	andi a3, a3, -8
	lbu a4, 0(a1)
	lbu a5, 1(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(a1)
	lbu a5, 5(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(a1)
	lbu a5, 9(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(a1)
	lbu a5, 13(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(a1)
	lbu a5, 17(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(a1)
	lbu a5, 21(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(a1)
	lbu a5, 25(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(a1)
	lbu a5, 29(a1)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(a1)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(a1)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 0(a2)
	lbu a5, 1(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 4(a2)
	lbu a5, 5(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 8(a2)
	lbu a5, 9(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 12(a2)
	lbu a5, 13(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 16(a2)
	lbu a5, 17(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 20(a2)
	lbu a5, 21(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 24(a2)
	lbu a5, 25(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 28(a2)
	lbu a5, 29(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 0(t5)
	lbu a5, 1(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 4(t5)
	lbu a5, 5(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 8(t5)
	lbu a5, 9(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 12(t5)
	lbu a5, 13(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 16(t5)
	lbu a5, 17(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 20(t5)
	lbu a5, 21(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 24(t5)
	lbu a5, 25(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 28(t5)
	lbu a5, 29(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	addi a7, zero, 38
	addi a5, zero, 0
	addi a4, zero, 0
	sw a4, 864(a3)
	sw a4, 868(a3)
	sw a4, 872(a3)
	sw a4, 876(a3)
	sw a4, 880(a3)
	sw a4, 884(a3)
	sw a4, 888(a3)
	sw a4, 892(a3)
	addi a6, a3, 0
	addi t0, zero, 8
20:
	lwu a1, 96(a6)
	addi a5, zero, 0
	lwu a2, 128(a3)
	mul a2, a1, a2
	lwu a4, 864(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 864(a6)
	srli a5, a4, 32
	lwu a2, 132(a3)
	mul a2, a1, a2
	lwu a4, 868(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 868(a6)
	srli a5, a4, 32
	lwu a2, 136(a3)
	mul a2, a1, a2
	lwu a4, 872(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 872(a6)
	srli a5, a4, 32
	lwu a2, 140(a3)
	mul a2, a1, a2
	lwu a4, 876(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 876(a6)
	srli a5, a4, 32
	lwu a2, 144(a3)
	mul a2, a1, a2
	lwu a4, 880(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 880(a6)
	srli a5, a4, 32
	lwu a2, 148(a3)
	mul a2, a1, a2
	lwu a4, 884(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 884(a6)
	srli a5, a4, 32
	lwu a2, 152(a3)
	mul a2, a1, a2
	lwu a4, 888(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 888(a6)
	srli a5, a4, 32
	lwu a2, 156(a3)
	mul a2, a1, a2
	lwu a4, 892(a6)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 892(a6)
	srli a5, a4, 32
	sw a5, 896(a6)
	addi a6, a6, 4
	addi t0, t0, -1
	bnez t0, 20b
	addi a5, zero, 0
	lwu a4, 864(a3)
	lwu a2, 64(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	lwu a2, 68(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	lwu a2, 72(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	lwu a2, 76(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	lwu a2, 80(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	lwu a2, 84(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	lwu a2, 88(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	lwu a2, 92(a3)
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	lwu a4, 896(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 900(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 904(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 908(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 912(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 916(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 920(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	addi t3, a3, 512
	lwu a4, 864(a3)
	sb a4, 0(t3)
	srli a5, a4, 8
	sb a5, 1(t3)
	srli a5, a4, 16
	sb a5, 2(t3)
	srli a5, a4, 24
	sb a5, 3(t3)
	lwu a4, 868(a3)
	sb a4, 4(t3)
	srli a5, a4, 8
	sb a5, 5(t3)
	srli a5, a4, 16
	sb a5, 6(t3)
	srli a5, a4, 24
	sb a5, 7(t3)
	lwu a4, 872(a3)
	sb a4, 8(t3)
	srli a5, a4, 8
	sb a5, 9(t3)
	srli a5, a4, 16
	sb a5, 10(t3)
	srli a5, a4, 24
	sb a5, 11(t3)
	lwu a4, 876(a3)
	sb a4, 12(t3)
	srli a5, a4, 8
	sb a5, 13(t3)
	srli a5, a4, 16
	sb a5, 14(t3)
	srli a5, a4, 24
	sb a5, 15(t3)
	lwu a4, 880(a3)
	sb a4, 16(t3)
	srli a5, a4, 8
	sb a5, 17(t3)
	srli a5, a4, 16
	sb a5, 18(t3)
	srli a5, a4, 24
	sb a5, 19(t3)
	lwu a4, 884(a3)
	sb a4, 20(t3)
	srli a5, a4, 8
	sb a5, 21(t3)
	srli a5, a4, 16
	sb a5, 22(t3)
	srli a5, a4, 24
	sb a5, 23(t3)
	lwu a4, 888(a3)
	sb a4, 24(t3)
	srli a5, a4, 8
	sb a5, 25(t3)
	srli a5, a4, 16
	sb a5, 26(t3)
	srli a5, a4, 24
	sb a5, 27(t3)
	lwu a4, 892(a3)
	sb a4, 28(t3)
	srli a5, a4, 8
	sb a5, 29(t3)
	srli a5, a4, 16
	sb a5, 30(t3)
	srli a5, a4, 24
	sb a5, 31(t3)
	lwu a4, 896(a3)
	sb a4, 32(t3)
	srli a5, a4, 8
	sb a5, 33(t3)
	srli a5, a4, 16
	sb a5, 34(t3)
	srli a5, a4, 24
	sb a5, 35(t3)
	lwu a4, 900(a3)
	sb a4, 36(t3)
	srli a5, a4, 8
	sb a5, 37(t3)
	srli a5, a4, 16
	sb a5, 38(t3)
	srli a5, a4, 24
	sb a5, 39(t3)
	lwu a4, 904(a3)
	sb a4, 40(t3)
	srli a5, a4, 8
	sb a5, 41(t3)
	srli a5, a4, 16
	sb a5, 42(t3)
	srli a5, a4, 24
	sb a5, 43(t3)
	lwu a4, 908(a3)
	sb a4, 44(t3)
	srli a5, a4, 8
	sb a5, 45(t3)
	srli a5, a4, 16
	sb a5, 46(t3)
	srli a5, a4, 24
	sb a5, 47(t3)
	lwu a4, 912(a3)
	sb a4, 48(t3)
	srli a5, a4, 8
	sb a5, 49(t3)
	srli a5, a4, 16
	sb a5, 50(t3)
	srli a5, a4, 24
	sb a5, 51(t3)
	lwu a4, 916(a3)
	sb a4, 52(t3)
	srli a5, a4, 8
	sb a5, 53(t3)
	srli a5, a4, 16
	sb a5, 54(t3)
	srli a5, a4, 24
	sb a5, 55(t3)
	lwu a4, 920(a3)
	sb a4, 56(t3)
	srli a5, a4, 8
	sb a5, 57(t3)
	srli a5, a4, 16
	sb a5, 58(t3)
	srli a5, a4, 24
	sb a5, 59(t3)
	lwu a4, 924(a3)
	sb a4, 60(t3)
	srli a5, a4, 8
	sb a5, 61(t3)
	srli a5, a4, 16
	sb a5, 62(t3)
	srli a5, a4, 24
	sb a5, 63(t3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t4, zero, 64
	lui t5, 360742
	addiw t5, t5, 794
	slli t5, t5, 32
	lui t0, 380765
	addiw t0, t0, 1005
	slli t0, t0, 32
	srli t0, t0, 32
	or t5, t5, t0
	lui t6, 85488
	addiw t6, t6, -1570
	slli t6, t6, 32
	lui t0, 667514
	addiw t0, t0, -810
	slli t0, t0, 32
	srli t0, t0, 32
	or t6, t6, t0
21:
	addi t4, t4, -8
	add a1, t3, t4
	lbu a2, 0(a1)
	lbu t0, 1(a1)
	slli t0, t0, 8
	or a2, a2, t0
	lbu t0, 2(a1)
	slli t0, t0, 16
	or a2, a2, t0
	lbu t0, 3(a1)
	slli t0, t0, 24
	or a2, a2, t0
	lbu t1, 4(a1)
	lbu t0, 5(a1)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(a1)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(a1)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or a2, a2, t1
	srli t0, a6, 60
	slli t1, a7, 4
	or t0, t0, t1
	srli t1, a7, 60
	slli a7, a6, 4
	srli a7, a7, 4
	addi a6, a5, 0
	addi a5, a4, 0
	addi a4, a2, 0
	mul t2, t0, t5
	mulhu a1, t0, t5
	mul a2, t0, t6
	mulhu t0, t0, t6
	add a1, a1, a2
	sltu a2, a1, a2
	add t0, t0, a2
	mul a2, t1, t5
	add a1, a1, a2
	sltu a2, a1, a2
	add t0, t0, a2
	mul a2, t1, t6
	add t0, t0, a2
	sltu a2, a4, t2
	sub a4, a4, t2
	sltu t1, a5, a1
	sub a5, a5, a1
	sltu t2, a5, a2
	sub a5, a5, a2
	or a2, t1, t2
	sltu t1, a6, t0
	sub a6, a6, t0
	sltu t2, a6, a2
	sub a6, a6, a2
	or a2, t1, t2
	sltu t1, a7, a2
	sub a7, a7, a2
	addi t2, zero, 0
	sub t2, t2, t1
	and a1, t5, t2
	add a4, a4, a1
	sltu a1, a4, a1
	and a2, t6, t2
	add a5, a5, a1
	sltu a1, a5, a1
	add a5, a5, a2
	sltu a2, a5, a2
	or a1, a1, a2
	add a6, a6, a1
	sltu a1, a6, a1
	add a7, a7, a1
	slli t1, t1, 60
	add a7, a7, t1
	bnez t4, 21b
	sd a4, 160(a3)
	sd a5, 168(a3)
	sd a6, 176(a3)
	sd a7, 184(a3)
	lwu a4, 160(a3)
	sb a4, 0(a0)
	srli a5, a4, 8
	sb a5, 1(a0)
	srli a5, a4, 16
	sb a5, 2(a0)
	srli a5, a4, 24
	sb a5, 3(a0)
	lwu a4, 164(a3)
	sb a4, 4(a0)
	srli a5, a4, 8
	sb a5, 5(a0)
	srli a5, a4, 16
	sb a5, 6(a0)
	srli a5, a4, 24
	sb a5, 7(a0)
	lwu a4, 168(a3)
	sb a4, 8(a0)
	srli a5, a4, 8
	sb a5, 9(a0)
	srli a5, a4, 16
	sb a5, 10(a0)
	srli a5, a4, 24
	sb a5, 11(a0)
	lwu a4, 172(a3)
	sb a4, 12(a0)
	srli a5, a4, 8
	sb a5, 13(a0)
	srli a5, a4, 16
	sb a5, 14(a0)
	srli a5, a4, 24
	sb a5, 15(a0)
	lwu a4, 176(a3)
	sb a4, 16(a0)
	srli a5, a4, 8
	sb a5, 17(a0)
	srli a5, a4, 16
	sb a5, 18(a0)
	srli a5, a4, 24
	sb a5, 19(a0)
	lwu a4, 180(a3)
	sb a4, 20(a0)
	srli a5, a4, 8
	sb a5, 21(a0)
	srli a5, a4, 16
	sb a5, 22(a0)
	srli a5, a4, 24
	sb a5, 23(a0)
	lwu a4, 184(a3)
	sb a4, 24(a0)
	srli a5, a4, 8
	sb a5, 25(a0)
	srli a5, a4, 16
	sb a5, 26(a0)
	srli a5, a4, 24
	sb a5, 27(a0)
	lwu a4, 188(a3)
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	ret
	.option pop
