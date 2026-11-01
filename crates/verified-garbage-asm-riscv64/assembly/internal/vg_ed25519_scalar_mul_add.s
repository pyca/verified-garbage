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
	sw a4, 160(a3)
	sw a4, 164(a3)
	sw a4, 168(a3)
	sw a4, 172(a3)
	sw a4, 176(a3)
	sw a4, 180(a3)
	sw a4, 184(a3)
	sw a4, 188(a3)
	addi t4, zero, 64
21:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 57
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 58
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 59
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 60
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 61
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 62
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 63
	srli a5, a5, 63
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
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	bnez t4, 21b
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
