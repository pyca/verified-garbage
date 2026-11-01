// The functions of `src/ed25519.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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

vg_ed25519_public_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi a3, sp, 0
	sd s7, 96(a3)
	sd s8, 104(a3)
	sd s9, 112(a3)
	sd s10, 120(a3)
	sd ra, 128(a3)
	addi s7, a0, 0
	addi s8, a1, 0
	addi s9, a2, 0
	addi s10, a3, 0
	addi a0, s9, 0
	call {vg_sha512_init}
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s8, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, s10, 0
	call {vg_sha512_finalize}
	ld a5, 0(s10)
	srli a5, a5, 3
	slli a5, a5, 3
	sd a5, 64(s10)
	ld a5, 8(s10)
	sd a5, 72(s10)
	ld a5, 16(s10)
	sd a5, 80(s10)
	ld a5, 24(s10)
	slli a5, a5, 2
	srli a5, a5, 2
	addi a6, zero, 1
	slli a6, a6, 62
	or a5, a5, a6
	sd a5, 88(s10)
	addi a0, s7, 0
	addi a1, s10, 64
	addi a2, s9, 0
	call {vg_ed25519_scalar_base}
	ld ra, 128(s10)
	ld s7, 96(s10)
	ld s8, 104(s10)
	ld s9, 112(s10)
	ld s10, 120(s10)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	addi sp, sp, 144
	ret
	.option pop

vg_ed25519_scalar_reduce:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi t3, a1, 0
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
20:
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
	bnez t4, 20b
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

vg_ed25519_scalar_base:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	sd s0, 1024(a3)
	sd s1, 1032(a3)
	sd s2, 1040(a3)
	sd s3, 1048(a3)
	sd s5, 1056(a3)
	sd s6, 1064(a3)
	sd ra, 1072(a3)
	addi s3, a0, 0
	addi s0, a1, 0
	addi a4, zero, 0
	sw a4, 64(a3)
	sw a4, 68(a3)
	sw a4, 72(a3)
	sw a4, 76(a3)
	sw a4, 80(a3)
	sw a4, 84(a3)
	sw a4, 88(a3)
	sw a4, 92(a3)
	sw a4, 96(a3)
	sw a4, 100(a3)
	sw a4, 104(a3)
	sw a4, 108(a3)
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
	sw a4, 280(a3)
	sw a4, 284(a3)
	sw a4, 288(a3)
	sw a4, 292(a3)
	sw a4, 296(a3)
	sw a4, 300(a3)
	sw a4, 304(a3)
	sw a4, 308(a3)
	sw a4, 312(a3)
	sw a4, 316(a3)
	sw a4, 320(a3)
	sw a4, 324(a3)
	sw a4, 328(a3)
	sw a4, 332(a3)
	sw a4, 336(a3)
	sw a4, 340(a3)
	sw a4, 344(a3)
	sw a4, 348(a3)
	sw a4, 352(a3)
	sw a4, 356(a3)
	sw a4, 360(a3)
	sw a4, 364(a3)
	sw a4, 368(a3)
	sw a4, 372(a3)
	sw a4, 376(a3)
	sw a4, 380(a3)
	sw a4, 384(a3)
	sw a4, 388(a3)
	sw a4, 392(a3)
	sw a4, 396(a3)
	sw a4, 400(a3)
	sw a4, 404(a3)
	sw a4, 408(a3)
	sw a4, 412(a3)
	sw a4, 416(a3)
	sw a4, 420(a3)
	sw a4, 424(a3)
	sw a4, 428(a3)
	sw a4, 432(a3)
	sw a4, 436(a3)
	sw a4, 440(a3)
	sw a4, 444(a3)
	sw a4, 448(a3)
	sw a4, 452(a3)
	sw a4, 456(a3)
	sw a4, 460(a3)
	sw a4, 464(a3)
	sw a4, 468(a3)
	sw a4, 472(a3)
	sw a4, 476(a3)
	sw a4, 480(a3)
	sw a4, 484(a3)
	sw a4, 488(a3)
	sw a4, 492(a3)
	sw a4, 496(a3)
	sw a4, 500(a3)
	sw a4, 504(a3)
	sw a4, 508(a3)
	sw a4, 512(a3)
	sw a4, 516(a3)
	sw a4, 520(a3)
	sw a4, 524(a3)
	sw a4, 528(a3)
	sw a4, 532(a3)
	sw a4, 536(a3)
	sw a4, 540(a3)
	sw a4, 544(a3)
	sw a4, 548(a3)
	sw a4, 552(a3)
	sw a4, 556(a3)
	sw a4, 560(a3)
	sw a4, 564(a3)
	sw a4, 568(a3)
	sw a4, 572(a3)
	sw a4, 576(a3)
	sw a4, 580(a3)
	sw a4, 584(a3)
	sw a4, 588(a3)
	sw a4, 592(a3)
	sw a4, 596(a3)
	sw a4, 600(a3)
	sw a4, 604(a3)
	sw a4, 608(a3)
	sw a4, 612(a3)
	sw a4, 616(a3)
	sw a4, 620(a3)
	sw a4, 624(a3)
	sw a4, 628(a3)
	sw a4, 632(a3)
	sw a4, 636(a3)
	sw a4, 640(a3)
	sw a4, 644(a3)
	sw a4, 648(a3)
	sw a4, 652(a3)
	sw a4, 656(a3)
	sw a4, 660(a3)
	sw a4, 664(a3)
	sw a4, 668(a3)
	sw a4, 672(a3)
	sw a4, 676(a3)
	sw a4, 680(a3)
	sw a4, 684(a3)
	sw a4, 688(a3)
	sw a4, 692(a3)
	sw a4, 696(a3)
	sw a4, 700(a3)
	sw a4, 704(a3)
	sw a4, 708(a3)
	sw a4, 712(a3)
	sw a4, 716(a3)
	sw a4, 720(a3)
	sw a4, 724(a3)
	sw a4, 728(a3)
	sw a4, 732(a3)
	sw a4, 736(a3)
	sw a4, 740(a3)
	sw a4, 744(a3)
	sw a4, 748(a3)
	sw a4, 752(a3)
	sw a4, 756(a3)
	sw a4, 760(a3)
	sw a4, 764(a3)
	lui a4, 586333
	addiw a4, a4, 1306
	sw a4, 64(a3)
	lui a4, 824675
	addiw a4, a4, -672
	sw a4, 68(a3)
	lui a4, 610906
	addiw a4, a4, 1970
	sw a4, 72(a3)
	lui a4, 430796
	addiw a4, a4, 1888
	sw a4, 76(a3)
	lui a4, 1039726
	addiw a4, a4, -932
	sw a4, 80(a3)
	lui a4, 789070
	addiw a4, a4, 561
	sw a4, 84(a3)
	lui a4, 841445
	addiw a4, a4, 1022
	sw a4, 88(a3)
	lui a4, 136851
	addiw a4, a4, 1747
	sw a4, 92(a3)
	lui a4, 419430
	addiw a4, a4, 1624
	sw a4, 96(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 100(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 104(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 108(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 112(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 116(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 120(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 678782
	addiw a4, a4, -605
	sw a4, 160(a3)
	lui a4, 450025
	addiw a4, a4, -1357
	sw a4, 164(a3)
	lui a4, 488725
	addiw a4, a4, 757
	sw a4, 168(a3)
	lui a4, 134922
	addiw a4, a4, -128
	sw a4, 172(a3)
	lui a4, 412350
	addiw a4, a4, 893
	sw a4, 176(a3)
	lui a4, 421541
	addiw a4, a4, -370
	sw a4, 180(a3)
	lui a4, 882871
	addiw a4, a4, 1637
	sw a4, 184(a3)
	lui a4, 424054
	addiw a4, a4, -241
	sw a4, 188(a3)
	addi s5, s0, 0
	lui a4, 79256
	addiw a4, a4, -1885
	sw a4, 576(a3)
	lui a4, 482997
	addiw a4, a4, -566
	sw a4, 580(a3)
	lui a4, 267294
	addiw a4, a4, -1877
	sw a4, 584(a3)
	lui a4, 1793
	addiw a4, a4, -1459
	sw a4, 588(a3)
	lui a4, 489375
	addiw a4, a4, -1896
	sw a4, 592(a3)
	lui a4, 576628
	addiw a4, a4, 121
	sw a4, 596(a3)
	lui a4, 177920
	addiw a4, a4, -397
	sw a4, 600(a3)
	lui a4, 335927
	addiw a4, a4, -786
	sw a4, 604(a3)
	addi s2, zero, 0
20:
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	addi s1, zero, 16
21:
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s1, s1, -1
	bnez s1, 21b
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 20b
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 64(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 68(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 72(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 76(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 80(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 84(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 88(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 92(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 96(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 100(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 104(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 108(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 112(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 116(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 120(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 160(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 164(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 168(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 172(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 176(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 180(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 184(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 188(a3)
	addi s6, zero, 16
22:
	addi s6, s6, -1
	addi s2, s6, 0
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi s2, zero, 0
23:
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 23b
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	slli a4, s6, 1
	add s0, s5, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	add a4, a4, a5
	slli a5, a4, 63
	srli a5, a5, 63
	sb a5, 32(a3)
	slli a5, a4, 62
	srli a5, a5, 63
	sb a5, 33(a3)
	slli a5, a4, 61
	srli a5, a5, 63
	sb a5, 34(a3)
	slli a5, a4, 60
	srli a5, a5, 63
	sb a5, 35(a3)
	slli a5, a4, 59
	srli a5, a5, 63
	sb a5, 36(a3)
	slli a5, a4, 58
	srli a5, a5, 63
	sb a5, 37(a3)
	slli a5, a4, 57
	srli a5, a5, 63
	sb a5, 38(a3)
	slli a5, a4, 56
	srli a5, a5, 63
	sb a5, 39(a3)
	slli a5, a4, 55
	srli a5, a5, 63
	sb a5, 40(a3)
	slli a5, a4, 54
	srli a5, a5, 63
	sb a5, 41(a3)
	slli a5, a4, 53
	srli a5, a5, 63
	sb a5, 42(a3)
	slli a5, a4, 52
	srli a5, a5, 63
	sb a5, 43(a3)
	slli a5, a4, 51
	srli a5, a5, 63
	sb a5, 44(a3)
	slli a5, a4, 50
	srli a5, a5, 63
	sb a5, 45(a3)
	slli a5, a4, 49
	srli a5, a5, 63
	sb a5, 46(a3)
	slli a5, a4, 48
	srli a5, a5, 63
	sb a5, 47(a3)
	addi s2, zero, 16
24:
	addi s2, s2, -1
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	add a4, a3, s2
	lbu a4, 32(a4)
	addi t0, a4, -1
	lwu a2, 64(a3)
	lwu a4, 608(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 64(a3)
	sw a4, 608(a3)
	lwu a2, 68(a3)
	lwu a4, 612(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 68(a3)
	sw a4, 612(a3)
	lwu a2, 72(a3)
	lwu a4, 616(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 72(a3)
	sw a4, 616(a3)
	lwu a2, 76(a3)
	lwu a4, 620(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 76(a3)
	sw a4, 620(a3)
	lwu a2, 80(a3)
	lwu a4, 624(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 80(a3)
	sw a4, 624(a3)
	lwu a2, 84(a3)
	lwu a4, 628(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 84(a3)
	sw a4, 628(a3)
	lwu a2, 88(a3)
	lwu a4, 632(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 88(a3)
	sw a4, 632(a3)
	lwu a2, 92(a3)
	lwu a4, 636(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 92(a3)
	sw a4, 636(a3)
	lwu a2, 96(a3)
	lwu a4, 640(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 96(a3)
	sw a4, 640(a3)
	lwu a2, 100(a3)
	lwu a4, 644(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 100(a3)
	sw a4, 644(a3)
	lwu a2, 104(a3)
	lwu a4, 648(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 104(a3)
	sw a4, 648(a3)
	lwu a2, 108(a3)
	lwu a4, 652(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 108(a3)
	sw a4, 652(a3)
	lwu a2, 112(a3)
	lwu a4, 656(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 656(a3)
	lwu a2, 116(a3)
	lwu a4, 660(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 660(a3)
	lwu a2, 120(a3)
	lwu a4, 664(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 664(a3)
	lwu a2, 124(a3)
	lwu a4, 668(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 668(a3)
	lwu a2, 128(a3)
	lwu a4, 672(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 672(a3)
	lwu a2, 132(a3)
	lwu a4, 676(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 676(a3)
	lwu a2, 136(a3)
	lwu a4, 680(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 680(a3)
	lwu a2, 140(a3)
	lwu a4, 684(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 684(a3)
	lwu a2, 144(a3)
	lwu a4, 688(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 688(a3)
	lwu a2, 148(a3)
	lwu a4, 692(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 692(a3)
	lwu a2, 152(a3)
	lwu a4, 696(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 696(a3)
	lwu a2, 156(a3)
	lwu a4, 700(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 700(a3)
	lwu a2, 160(a3)
	lwu a4, 704(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 704(a3)
	lwu a2, 164(a3)
	lwu a4, 708(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 708(a3)
	lwu a2, 168(a3)
	lwu a4, 712(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 712(a3)
	lwu a2, 172(a3)
	lwu a4, 716(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 716(a3)
	lwu a2, 176(a3)
	lwu a4, 720(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 720(a3)
	lwu a2, 180(a3)
	lwu a4, 724(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 724(a3)
	lwu a2, 184(a3)
	lwu a4, 728(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 728(a3)
	lwu a2, 188(a3)
	lwu a4, 732(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 732(a3)
	bnez s2, 24b
	bnez s6, 22b
	addi a0, a3, 0
	call {vg_gf25519_r32_pow250}
	addi a3, a0, 0
	addi t1, zero, 5
25:
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 864(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 544(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 864(a3)
	srli a7, a5, 63
	ld a5, 872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 872(a3)
	srli a7, a5, 63
	ld a5, 880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 552(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 880(a3)
	srli a7, a5, 63
	ld a5, 888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 888(a3)
	srli a7, a5, 63
	ld a5, 896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 560(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 896(a3)
	srli a7, a5, 63
	ld a5, 904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 904(a3)
	srli a7, a5, 63
	ld a5, 912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 568(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 912(a3)
	srli a7, a5, 63
	ld a5, 920(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 920(a3)
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 544(a3)
	sd t4, 552(a3)
	sd t5, 560(a3)
	sd t6, 568(a3)
	addi t1, t1, -1
	bnez t1, 25b
	addi a0, a3, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 512
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 64
	addi a2, zero, 64
	addi a3, zero, 544
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 96
	addi a2, zero, 96
	addi a3, zero, 544
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli t6, a4, 63
	srli t6, t6, 32
	lwu a4, 96(a3)
	sw a4, 864(a3)
	lwu a4, 100(a3)
	sw a4, 868(a3)
	lwu a4, 104(a3)
	sw a4, 872(a3)
	lwu a4, 108(a3)
	sw a4, 876(a3)
	lwu a4, 112(a3)
	sw a4, 880(a3)
	lwu a4, 116(a3)
	sw a4, 884(a3)
	lwu a4, 120(a3)
	sw a4, 888(a3)
	lwu a4, 124(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 892(a3)
	add a4, a4, t6
	sw a4, 892(a3)
	addi s0, s3, 0
	lwu a4, 864(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 868(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 872(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 876(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 880(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 884(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 888(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 892(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	ld s0, 1024(a3)
	ld s1, 1032(a3)
	ld s2, 1040(a3)
	ld s3, 1048(a3)
	ld s5, 1056(a3)
	ld s6, 1064(a3)
	ld ra, 1072(a3)
	ret
	.option pop

vg_ed25519_sign_cached:
	.option push
	.option arch, +m, +c
	addi sp, sp, -288
	addi a6, sp, 0
	sd s1, 224(a6)
	sd s7, 232(a6)
	sd s8, 240(a6)
	sd s9, 248(a6)
	sd s10, 256(a6)
	sd s11, 264(a6)
	sd ra, 272(a6)
	addi s7, a0, 0
	addi s1, a1, 0
	addi s8, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	lbu a5, 0(a2)
	sb a5, 192(s11)
	lbu a5, 1(a2)
	sb a5, 193(s11)
	lbu a5, 2(a2)
	sb a5, 194(s11)
	lbu a5, 3(a2)
	sb a5, 195(s11)
	lbu a5, 4(a2)
	sb a5, 196(s11)
	lbu a5, 5(a2)
	sb a5, 197(s11)
	lbu a5, 6(a2)
	sb a5, 198(s11)
	lbu a5, 7(a2)
	sb a5, 199(s11)
	lbu a5, 8(a2)
	sb a5, 200(s11)
	lbu a5, 9(a2)
	sb a5, 201(s11)
	lbu a5, 10(a2)
	sb a5, 202(s11)
	lbu a5, 11(a2)
	sb a5, 203(s11)
	lbu a5, 12(a2)
	sb a5, 204(s11)
	lbu a5, 13(a2)
	sb a5, 205(s11)
	lbu a5, 14(a2)
	sb a5, 206(s11)
	lbu a5, 15(a2)
	sb a5, 207(s11)
	lbu a5, 16(a2)
	sb a5, 208(s11)
	lbu a5, 17(a2)
	sb a5, 209(s11)
	lbu a5, 18(a2)
	sb a5, 210(s11)
	lbu a5, 19(a2)
	sb a5, 211(s11)
	lbu a5, 20(a2)
	sb a5, 212(s11)
	lbu a5, 21(a2)
	sb a5, 213(s11)
	lbu a5, 22(a2)
	sb a5, 214(s11)
	lbu a5, 23(a2)
	sb a5, 215(s11)
	lbu a5, 24(a2)
	sb a5, 216(s11)
	lbu a5, 25(a2)
	sb a5, 217(s11)
	lbu a5, 26(a2)
	sb a5, 218(s11)
	lbu a5, 27(a2)
	sb a5, 219(s11)
	lbu a5, 28(a2)
	sb a5, 220(s11)
	lbu a5, 29(a2)
	sb a5, 221(s11)
	lbu a5, 30(a2)
	sb a5, 222(s11)
	lbu a5, 31(a2)
	sb a5, 223(s11)
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s1, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s11, 128
	call {vg_sha512_finalize}
	ld a5, 128(s11)
	srli a5, a5, 3
	slli a5, a5, 3
	sd a5, 0(s11)
	ld a5, 136(s11)
	sd a5, 8(s11)
	ld a5, 144(s11)
	sd a5, 16(s11)
	ld a5, 152(s11)
	slli a5, a5, 2
	srli a5, a5, 2
	addi a6, zero, 1
	slli a6, a6, 62
	or a5, a5, a6
	sd a5, 24(s11)
	ld a5, 160(s11)
	sd a5, 32(s11)
	ld a5, 168(s11)
	sd a5, 40(s11)
	ld a5, 176(s11)
	sd a5, 48(s11)
	ld a5, 184(s11)
	sd a5, 56(s11)
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s11, 32
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s8, 0
	addi a3, s9, 0
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, s9, 32
	addi a2, s11, 128
	call {vg_sha512_finalize}
	addi a0, s11, 64
	addi a1, s11, 128
	addi a2, s10, 0
	call {vg_ed25519_scalar_reduce}
	addi a0, s7, 0
	addi a1, s11, 64
	addi a2, s10, 0
	call {vg_ed25519_scalar_base}
	addi a0, s10, 0
	call {vg_sha512_init}
	addi a0, s10, 0
	addi a1, zero, 0
	addi a2, s7, 0
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 32
	addi a2, s11, 192
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, zero, 64
	addi a2, s8, 0
	addi a3, s9, 0
	call {vg_sha512_update}
	addi a0, s10, 0
	addi a1, s9, 64
	addi a2, s11, 128
	call {vg_sha512_finalize}
	addi a0, s11, 96
	addi a1, s11, 128
	addi a2, s10, 0
	call {vg_ed25519_scalar_reduce}
	addi a0, s7, 32
	addi a1, s11, 64
	addi a2, s11, 96
	addi a3, s11, 0
	addi a4, s10, 0
	call {vg_ed25519_scalar_mul_add}
	ld ra, 272(s11)
	ld s1, 224(s11)
	ld s7, 232(s11)
	ld s8, 240(s11)
	ld s9, 248(s11)
	ld s10, 256(s11)
	ld s11, 264(s11)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	addi sp, sp, 288
	ret
	.option pop

vg_ed25519_verify_equation:
	.option push
	.option arch, +m, +c
	sd s0, 1024(a3)
	sd s1, 1032(a3)
	sd s2, 1040(a3)
	sd s3, 1048(a3)
	sd s4, 1056(a3)
	sd s5, 1064(a3)
	sd s6, 1072(a3)
	sd s7, 1080(a3)
	sd s8, 1088(a3)
	sd s9, 1096(a3)
	sd s10, 1104(a3)
	sd s11, 1112(a3)
	sd ra, 1120(a3)
	addi s9, a0, 0
	addi s10, a1, 0
	addi s11, a2, 0
	addi s0, s10, 32
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
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
	beqz a5, 20f
	addi s3, zero, 0
	j 21f
20:
	addi a4, zero, 0
	sw a4, 64(a3)
	sw a4, 68(a3)
	sw a4, 72(a3)
	sw a4, 76(a3)
	sw a4, 80(a3)
	sw a4, 84(a3)
	sw a4, 88(a3)
	sw a4, 92(a3)
	sw a4, 96(a3)
	sw a4, 100(a3)
	sw a4, 104(a3)
	sw a4, 108(a3)
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
	sw a4, 280(a3)
	sw a4, 284(a3)
	sw a4, 288(a3)
	sw a4, 292(a3)
	sw a4, 296(a3)
	sw a4, 300(a3)
	sw a4, 304(a3)
	sw a4, 308(a3)
	sw a4, 312(a3)
	sw a4, 316(a3)
	sw a4, 320(a3)
	sw a4, 324(a3)
	sw a4, 328(a3)
	sw a4, 332(a3)
	sw a4, 336(a3)
	sw a4, 340(a3)
	sw a4, 344(a3)
	sw a4, 348(a3)
	sw a4, 352(a3)
	sw a4, 356(a3)
	sw a4, 360(a3)
	sw a4, 364(a3)
	sw a4, 368(a3)
	sw a4, 372(a3)
	sw a4, 376(a3)
	sw a4, 380(a3)
	sw a4, 384(a3)
	sw a4, 388(a3)
	sw a4, 392(a3)
	sw a4, 396(a3)
	sw a4, 400(a3)
	sw a4, 404(a3)
	sw a4, 408(a3)
	sw a4, 412(a3)
	sw a4, 416(a3)
	sw a4, 420(a3)
	sw a4, 424(a3)
	sw a4, 428(a3)
	sw a4, 432(a3)
	sw a4, 436(a3)
	sw a4, 440(a3)
	sw a4, 444(a3)
	sw a4, 448(a3)
	sw a4, 452(a3)
	sw a4, 456(a3)
	sw a4, 460(a3)
	sw a4, 464(a3)
	sw a4, 468(a3)
	sw a4, 472(a3)
	sw a4, 476(a3)
	sw a4, 480(a3)
	sw a4, 484(a3)
	sw a4, 488(a3)
	sw a4, 492(a3)
	sw a4, 496(a3)
	sw a4, 500(a3)
	sw a4, 504(a3)
	sw a4, 508(a3)
	sw a4, 512(a3)
	sw a4, 516(a3)
	sw a4, 520(a3)
	sw a4, 524(a3)
	sw a4, 528(a3)
	sw a4, 532(a3)
	sw a4, 536(a3)
	sw a4, 540(a3)
	sw a4, 544(a3)
	sw a4, 548(a3)
	sw a4, 552(a3)
	sw a4, 556(a3)
	sw a4, 560(a3)
	sw a4, 564(a3)
	sw a4, 568(a3)
	sw a4, 572(a3)
	sw a4, 576(a3)
	sw a4, 580(a3)
	sw a4, 584(a3)
	sw a4, 588(a3)
	sw a4, 592(a3)
	sw a4, 596(a3)
	sw a4, 600(a3)
	sw a4, 604(a3)
	sw a4, 608(a3)
	sw a4, 612(a3)
	sw a4, 616(a3)
	sw a4, 620(a3)
	sw a4, 624(a3)
	sw a4, 628(a3)
	sw a4, 632(a3)
	sw a4, 636(a3)
	sw a4, 640(a3)
	sw a4, 644(a3)
	sw a4, 648(a3)
	sw a4, 652(a3)
	sw a4, 656(a3)
	sw a4, 660(a3)
	sw a4, 664(a3)
	sw a4, 668(a3)
	sw a4, 672(a3)
	sw a4, 676(a3)
	sw a4, 680(a3)
	sw a4, 684(a3)
	sw a4, 688(a3)
	sw a4, 692(a3)
	sw a4, 696(a3)
	sw a4, 700(a3)
	sw a4, 704(a3)
	sw a4, 708(a3)
	sw a4, 712(a3)
	sw a4, 716(a3)
	sw a4, 720(a3)
	sw a4, 724(a3)
	sw a4, 728(a3)
	sw a4, 732(a3)
	sw a4, 736(a3)
	sw a4, 740(a3)
	sw a4, 744(a3)
	sw a4, 748(a3)
	sw a4, 752(a3)
	sw a4, 756(a3)
	sw a4, 760(a3)
	sw a4, 764(a3)
	addi s7, s9, 0
	lui s8, 2
	addiw s8, s8, -416
	addi s4, zero, 1
22:
	addi s0, s7, 0
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lwu a4, 124(a3)
	srli a5, a4, 31
	sw a5, 24(a3)
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 124(a3)
	lwu a4, 96(a3)
	sw a4, 864(a3)
	lwu a4, 100(a3)
	sw a4, 868(a3)
	lwu a4, 104(a3)
	sw a4, 872(a3)
	lwu a4, 108(a3)
	sw a4, 876(a3)
	lwu a4, 112(a3)
	sw a4, 880(a3)
	lwu a4, 116(a3)
	sw a4, 884(a3)
	lwu a4, 120(a3)
	sw a4, 888(a3)
	lwu a4, 124(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 96(a3)
	lwu a5, 864(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 100(a3)
	lwu a5, 868(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 104(a3)
	lwu a5, 872(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 108(a3)
	lwu a5, 876(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 112(a3)
	lwu a5, 880(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 116(a3)
	lwu a5, 884(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 120(a3)
	lwu a5, 888(a3)
	xor a4, a4, a5
	or a2, a2, a4
	lwu a4, 124(a3)
	lwu a5, 892(a3)
	xor a4, a4, a5
	or a2, a2, a4
	beqz a2, 23f
	addi s3, zero, 0
	j 24f
23:
	lui a4, 79256
	addiw a4, a4, -1885
	sw a4, 576(a3)
	lui a4, 482997
	addiw a4, a4, -566
	sw a4, 580(a3)
	lui a4, 267294
	addiw a4, a4, -1877
	sw a4, 584(a3)
	lui a4, 1793
	addiw a4, a4, -1459
	sw a4, 588(a3)
	lui a4, 489375
	addiw a4, a4, -1896
	sw a4, 592(a3)
	lui a4, 576628
	addiw a4, a4, 121
	sw a4, 596(a3)
	lui a4, 177920
	addiw a4, a4, -397
	sw a4, 600(a3)
	lui a4, 335927
	addiw a4, a4, -786
	sw a4, 604(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 192(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 196(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 200(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 204(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 208(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 212(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 216(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 220(a3)
	addi a0, a3, 0
	addi a1, zero, 224
	addi a2, zero, 96
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	ld t3, 224(a3)
	ld a7, 192(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 200(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 208(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 216(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 256(a3)
	sd t4, 264(a3)
	sd t5, 272(a3)
	sd t6, 280(a3)
	addi a0, a3, 0
	addi a1, zero, 288
	addi a2, zero, 576
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 288
	addi a2, zero, 288
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	ld t3, 288(a3)
	ld a7, 192(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 296(a3)
	ld a7, 200(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 304(a3)
	ld a7, 208(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 312(a3)
	ld a7, 216(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 288(a3)
	sd t4, 296(a3)
	sd t5, 304(a3)
	sd t6, 312(a3)
	addi a0, a3, 0
	addi a1, zero, 320
	addi a2, zero, 288
	addi a3, zero, 288
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 352
	addi a2, zero, 320
	addi a3, zero, 288
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 384
	addi a2, zero, 352
	addi a3, zero, 352
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 384
	addi a2, zero, 384
	addi a3, zero, 288
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 128
	addi a2, zero, 256
	addi a3, zero, 384
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	call {vg_gf25519_r32_pow250}
	addi a3, a0, 0
	addi t1, zero, 2
25:
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 864(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 864(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 544(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 864(a3)
	srli a7, a5, 63
	ld a5, 872(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 872(a3)
	srli a7, a5, 63
	ld a5, 880(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 552(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 880(a3)
	srli a7, a5, 63
	ld a5, 888(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 888(a3)
	srli a7, a5, 63
	ld a5, 896(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 560(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 896(a3)
	srli a7, a5, 63
	ld a5, 904(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 904(a3)
	srli a7, a5, 63
	ld a5, 912(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 568(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 912(a3)
	srli a7, a5, 63
	ld a5, 920(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 920(a3)
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 544(a3)
	sd t4, 552(a3)
	sd t5, 560(a3)
	sd t6, 568(a3)
	addi t1, t1, -1
	bnez t1, 25b
	addi a0, a3, 0
	addi a1, zero, 544
	addi a2, zero, 544
	addi a3, zero, 128
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 224(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 228(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 232(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 236(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 240(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 244(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 248(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 252(a3)
	ld t3, 224(a3)
	ld a7, 256(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 264(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 272(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 280(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 448(a3)
	sd t4, 456(a3)
	sd t5, 464(a3)
	sd t6, 472(a3)
	addi a0, a3, 0
	addi a1, zero, 64
	addi a2, zero, 256
	addi a3, zero, 352
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 64
	addi a2, zero, 64
	addi a3, zero, 544
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 416
	addi a2, zero, 288
	addi a3, zero, 64
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 416
	addi a2, zero, 416
	addi a3, zero, 64
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	ld t3, 416(a3)
	ld a7, 256(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 424(a3)
	ld a7, 264(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 272(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 280(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 736(a3)
	sd t4, 744(a3)
	sd t5, 752(a3)
	sd t6, 760(a3)
	lwu a4, 736(a3)
	sw a4, 864(a3)
	lwu a4, 740(a3)
	sw a4, 868(a3)
	lwu a4, 744(a3)
	sw a4, 872(a3)
	lwu a4, 748(a3)
	sw a4, 876(a3)
	lwu a4, 752(a3)
	sw a4, 880(a3)
	lwu a4, 756(a3)
	sw a4, 884(a3)
	lwu a4, 760(a3)
	sw a4, 888(a3)
	lwu a4, 764(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 26f
	ld t3, 416(a3)
	ld a7, 448(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 424(a3)
	ld a7, 456(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 464(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 472(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 736(a3)
	sd t4, 744(a3)
	sd t5, 752(a3)
	sd t6, 760(a3)
	lwu a4, 736(a3)
	sw a4, 864(a3)
	lwu a4, 740(a3)
	sw a4, 868(a3)
	lwu a4, 744(a3)
	sw a4, 872(a3)
	lwu a4, 748(a3)
	sw a4, 876(a3)
	lwu a4, 752(a3)
	sw a4, 880(a3)
	lwu a4, 756(a3)
	sw a4, 884(a3)
	lwu a4, 760(a3)
	sw a4, 888(a3)
	lwu a4, 764(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 28f
	addi s3, zero, 0
	j 29f
28:
	lui a4, 303338
	addiw a4, a4, 176
	sw a4, 640(a3)
	lui a4, 806626
	addiw a4, a4, -1241
	sw a4, 644(a3)
	lui a4, 709374
	addiw a4, a4, 1144
	sw a4, 648(a3)
	lui a4, 193586
	addiw a4, a4, -2042
	sw a4, 652(a3)
	lui a4, 253885
	addiw a4, a4, 1959
	sw a4, 656(a3)
	lui a4, 177360
	addiw a4, a4, 153
	sw a4, 660(a3)
	lui a4, 326686
	addiw a4, a4, -245
	sw a4, 664(a3)
	lui a4, 178226
	addiw a4, a4, 1152
	sw a4, 668(a3)
	addi a0, a3, 0
	addi a1, zero, 64
	addi a2, zero, 64
	addi a3, zero, 640
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 210f
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli a4, a4, 63
	srli a4, a4, 63
	lwu a5, 24(a3)
	xor a2, a4, a5
	beqz a2, 212f
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 224(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 228(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 232(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 236(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 240(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 244(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 248(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 252(a3)
	ld t3, 224(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	j 213f
212:
213:
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	addi a0, a3, 0
	addi a1, zero, 160
	addi a2, zero, 64
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi s3, zero, 1
	j 211f
210:
	lwu a2, 24(a3)
	bnez a2, 214f
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli a4, a4, 63
	srli a4, a4, 63
	lwu a5, 24(a3)
	xor a2, a4, a5
	beqz a2, 216f
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 224(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 228(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 232(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 236(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 240(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 244(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 248(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 252(a3)
	ld t3, 224(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	j 217f
216:
217:
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	addi a0, a3, 0
	addi a1, zero, 160
	addi a2, zero, 64
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi s3, zero, 1
	j 215f
214:
	addi s3, zero, 0
215:
211:
29:
	j 27f
26:
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 218f
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli a4, a4, 63
	srli a4, a4, 63
	lwu a5, 24(a3)
	xor a2, a4, a5
	beqz a2, 220f
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 224(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 228(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 232(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 236(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 240(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 244(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 248(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 252(a3)
	ld t3, 224(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	j 221f
220:
221:
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	addi a0, a3, 0
	addi a1, zero, 160
	addi a2, zero, 64
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi s3, zero, 1
	j 219f
218:
	lwu a2, 24(a3)
	bnez a2, 222f
	lwu a4, 64(a3)
	sw a4, 864(a3)
	lwu a4, 68(a3)
	sw a4, 868(a3)
	lwu a4, 72(a3)
	sw a4, 872(a3)
	lwu a4, 76(a3)
	sw a4, 876(a3)
	lwu a4, 80(a3)
	sw a4, 880(a3)
	lwu a4, 84(a3)
	sw a4, 884(a3)
	lwu a4, 88(a3)
	sw a4, 888(a3)
	lwu a4, 92(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	lwu a4, 864(a3)
	slli a4, a4, 63
	srli a4, a4, 63
	lwu a5, 24(a3)
	xor a2, a4, a5
	beqz a2, 224f
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 224(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 228(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 232(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 236(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 240(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 244(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 248(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 252(a3)
	ld t3, 224(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	j 225f
224:
225:
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	addi a0, a3, 0
	addi a1, zero, 160
	addi a2, zero, 64
	addi a3, zero, 96
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi s3, zero, 1
	j 223f
222:
	addi s3, zero, 0
223:
219:
27:
24:
	and s4, s4, s3
	add s0, a3, s8
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	addi s7, s10, 0
	addi s8, s8, 128
	lui a4, 2
	addiw a4, a4, -160
	sub a4, s8, a4
	bnez a4, 22b
	bnez s4, 226f
	addi s3, zero, 0
	j 227f
226:
	addi s0, s10, 32
	lui a4, 586333
	addiw a4, a4, 1306
	sw a4, 64(a3)
	lui a4, 824675
	addiw a4, a4, -672
	sw a4, 68(a3)
	lui a4, 610906
	addiw a4, a4, 1970
	sw a4, 72(a3)
	lui a4, 430796
	addiw a4, a4, 1888
	sw a4, 76(a3)
	lui a4, 1039726
	addiw a4, a4, -932
	sw a4, 80(a3)
	lui a4, 789070
	addiw a4, a4, 561
	sw a4, 84(a3)
	lui a4, 841445
	addiw a4, a4, 1022
	sw a4, 88(a3)
	lui a4, 136851
	addiw a4, a4, 1747
	sw a4, 92(a3)
	lui a4, 419430
	addiw a4, a4, 1624
	sw a4, 96(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 100(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 104(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 108(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 112(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 116(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 120(a3)
	lui a4, 419430
	addiw a4, a4, 1638
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 678782
	addiw a4, a4, -605
	sw a4, 160(a3)
	lui a4, 450025
	addiw a4, a4, -1357
	sw a4, 164(a3)
	lui a4, 488725
	addiw a4, a4, 757
	sw a4, 168(a3)
	lui a4, 134922
	addiw a4, a4, -128
	sw a4, 172(a3)
	lui a4, 412350
	addiw a4, a4, 893
	sw a4, 176(a3)
	lui a4, 421541
	addiw a4, a4, -370
	sw a4, 180(a3)
	lui a4, 882871
	addiw a4, a4, 1637
	sw a4, 184(a3)
	lui a4, 424054
	addiw a4, a4, -241
	sw a4, 188(a3)
	addi s5, s0, 0
	lui a4, 79256
	addiw a4, a4, -1885
	sw a4, 576(a3)
	lui a4, 482997
	addiw a4, a4, -566
	sw a4, 580(a3)
	lui a4, 267294
	addiw a4, a4, -1877
	sw a4, 584(a3)
	lui a4, 1793
	addiw a4, a4, -1459
	sw a4, 588(a3)
	lui a4, 489375
	addiw a4, a4, -1896
	sw a4, 592(a3)
	lui a4, 576628
	addiw a4, a4, 121
	sw a4, 596(a3)
	lui a4, 177920
	addiw a4, a4, -397
	sw a4, 600(a3)
	lui a4, 335927
	addiw a4, a4, -786
	sw a4, 604(a3)
	addi s2, zero, 0
228:
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	addi s1, zero, 16
229:
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s1, s1, -1
	bnez s1, 229b
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 228b
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 64(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 68(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 72(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 76(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 80(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 84(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 88(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 92(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 96(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 100(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 104(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 108(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 112(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 116(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 120(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 160(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 164(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 168(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 172(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 176(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 180(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 184(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 188(a3)
	addi s6, zero, 16
230:
	addi s6, s6, -1
	addi s2, s6, 0
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi s2, zero, 0
231:
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 231b
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	slli a4, s6, 1
	add s0, s5, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	add a4, a4, a5
	slli a5, a4, 63
	srli a5, a5, 63
	sb a5, 32(a3)
	slli a5, a4, 62
	srli a5, a5, 63
	sb a5, 33(a3)
	slli a5, a4, 61
	srli a5, a5, 63
	sb a5, 34(a3)
	slli a5, a4, 60
	srli a5, a5, 63
	sb a5, 35(a3)
	slli a5, a4, 59
	srli a5, a5, 63
	sb a5, 36(a3)
	slli a5, a4, 58
	srli a5, a5, 63
	sb a5, 37(a3)
	slli a5, a4, 57
	srli a5, a5, 63
	sb a5, 38(a3)
	slli a5, a4, 56
	srli a5, a5, 63
	sb a5, 39(a3)
	slli a5, a4, 55
	srli a5, a5, 63
	sb a5, 40(a3)
	slli a5, a4, 54
	srli a5, a5, 63
	sb a5, 41(a3)
	slli a5, a4, 53
	srli a5, a5, 63
	sb a5, 42(a3)
	slli a5, a4, 52
	srli a5, a5, 63
	sb a5, 43(a3)
	slli a5, a4, 51
	srli a5, a5, 63
	sb a5, 44(a3)
	slli a5, a4, 50
	srli a5, a5, 63
	sb a5, 45(a3)
	slli a5, a4, 49
	srli a5, a5, 63
	sb a5, 46(a3)
	slli a5, a4, 48
	srli a5, a5, 63
	sb a5, 47(a3)
	addi s2, zero, 16
232:
	addi s2, s2, -1
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	add a4, a3, s2
	lbu a4, 32(a4)
	addi t0, a4, -1
	lwu a2, 64(a3)
	lwu a4, 608(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 64(a3)
	sw a4, 608(a3)
	lwu a2, 68(a3)
	lwu a4, 612(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 68(a3)
	sw a4, 612(a3)
	lwu a2, 72(a3)
	lwu a4, 616(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 72(a3)
	sw a4, 616(a3)
	lwu a2, 76(a3)
	lwu a4, 620(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 76(a3)
	sw a4, 620(a3)
	lwu a2, 80(a3)
	lwu a4, 624(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 80(a3)
	sw a4, 624(a3)
	lwu a2, 84(a3)
	lwu a4, 628(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 84(a3)
	sw a4, 628(a3)
	lwu a2, 88(a3)
	lwu a4, 632(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 88(a3)
	sw a4, 632(a3)
	lwu a2, 92(a3)
	lwu a4, 636(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 92(a3)
	sw a4, 636(a3)
	lwu a2, 96(a3)
	lwu a4, 640(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 96(a3)
	sw a4, 640(a3)
	lwu a2, 100(a3)
	lwu a4, 644(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 100(a3)
	sw a4, 644(a3)
	lwu a2, 104(a3)
	lwu a4, 648(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 104(a3)
	sw a4, 648(a3)
	lwu a2, 108(a3)
	lwu a4, 652(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 108(a3)
	sw a4, 652(a3)
	lwu a2, 112(a3)
	lwu a4, 656(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 656(a3)
	lwu a2, 116(a3)
	lwu a4, 660(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 660(a3)
	lwu a2, 120(a3)
	lwu a4, 664(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 664(a3)
	lwu a2, 124(a3)
	lwu a4, 668(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 668(a3)
	lwu a2, 128(a3)
	lwu a4, 672(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 672(a3)
	lwu a2, 132(a3)
	lwu a4, 676(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 676(a3)
	lwu a2, 136(a3)
	lwu a4, 680(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 680(a3)
	lwu a2, 140(a3)
	lwu a4, 684(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 684(a3)
	lwu a2, 144(a3)
	lwu a4, 688(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 688(a3)
	lwu a2, 148(a3)
	lwu a4, 692(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 692(a3)
	lwu a2, 152(a3)
	lwu a4, 696(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 696(a3)
	lwu a2, 156(a3)
	lwu a4, 700(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 700(a3)
	lwu a2, 160(a3)
	lwu a4, 704(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 704(a3)
	lwu a2, 164(a3)
	lwu a4, 708(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 708(a3)
	lwu a2, 168(a3)
	lwu a4, 712(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 712(a3)
	lwu a2, 172(a3)
	lwu a4, 716(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 716(a3)
	lwu a2, 176(a3)
	lwu a4, 720(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 720(a3)
	lwu a2, 180(a3)
	lwu a4, 724(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 724(a3)
	lwu a2, 184(a3)
	lwu a4, 728(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 728(a3)
	lwu a2, 188(a3)
	lwu a4, 732(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 732(a3)
	bnez s2, 232b
	bnez s6, 230b
	lui s0, 2
	addiw s0, s0, -160
	add s0, a3, s0
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	lui s0, 2
	addiw s0, s0, -416
	add s0, a3, s0
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi s0, s11, 0
	addi s5, s0, 0
	lui a4, 79256
	addiw a4, a4, -1885
	sw a4, 576(a3)
	lui a4, 482997
	addiw a4, a4, -566
	sw a4, 580(a3)
	lui a4, 267294
	addiw a4, a4, -1877
	sw a4, 584(a3)
	lui a4, 1793
	addiw a4, a4, -1459
	sw a4, 588(a3)
	lui a4, 489375
	addiw a4, a4, -1896
	sw a4, 592(a3)
	lui a4, 576628
	addiw a4, a4, 121
	sw a4, 596(a3)
	lui a4, 177920
	addiw a4, a4, -397
	sw a4, 600(a3)
	lui a4, 335927
	addiw a4, a4, -786
	sw a4, 604(a3)
	addi s2, zero, 0
233:
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	addi s1, zero, 16
234:
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s1, s1, -1
	bnez s1, 234b
	addi s2, s2, 1
	addi a4, s2, -32
	bnez a4, 233b
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 64(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 68(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 72(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 76(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 80(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 84(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 88(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 92(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 96(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 100(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 104(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 108(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 112(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 116(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 120(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 124(a3)
	lui a4, 0
	addiw a4, a4, 1
	sw a4, 128(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 132(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 136(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 140(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 144(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 148(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 152(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 156(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 160(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 164(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 168(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 172(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 176(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 180(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 184(a3)
	lui a4, 0
	addiw a4, a4, 0
	sw a4, 188(a3)
	addi s6, zero, 32
235:
	addi s6, s6, -1
	addi s2, s6, 0
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 0
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi s2, zero, 0
236:
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lwu a4, 64(a3)
	sb a4, 0(s0)
	srli a5, a4, 8
	sb a5, 1(s0)
	srli a5, a4, 16
	sb a5, 2(s0)
	srli a5, a4, 24
	sb a5, 3(s0)
	lwu a4, 68(a3)
	sb a4, 4(s0)
	srli a5, a4, 8
	sb a5, 5(s0)
	srli a5, a4, 16
	sb a5, 6(s0)
	srli a5, a4, 24
	sb a5, 7(s0)
	lwu a4, 72(a3)
	sb a4, 8(s0)
	srli a5, a4, 8
	sb a5, 9(s0)
	srli a5, a4, 16
	sb a5, 10(s0)
	srli a5, a4, 24
	sb a5, 11(s0)
	lwu a4, 76(a3)
	sb a4, 12(s0)
	srli a5, a4, 8
	sb a5, 13(s0)
	srli a5, a4, 16
	sb a5, 14(s0)
	srli a5, a4, 24
	sb a5, 15(s0)
	lwu a4, 80(a3)
	sb a4, 16(s0)
	srli a5, a4, 8
	sb a5, 17(s0)
	srli a5, a4, 16
	sb a5, 18(s0)
	srli a5, a4, 24
	sb a5, 19(s0)
	lwu a4, 84(a3)
	sb a4, 20(s0)
	srli a5, a4, 8
	sb a5, 21(s0)
	srli a5, a4, 16
	sb a5, 22(s0)
	srli a5, a4, 24
	sb a5, 23(s0)
	lwu a4, 88(a3)
	sb a4, 24(s0)
	srli a5, a4, 8
	sb a5, 25(s0)
	srli a5, a4, 16
	sb a5, 26(s0)
	srli a5, a4, 24
	sb a5, 27(s0)
	lwu a4, 92(a3)
	sb a4, 28(s0)
	srli a5, a4, 8
	sb a5, 29(s0)
	srli a5, a4, 16
	sb a5, 30(s0)
	srli a5, a4, 24
	sb a5, 31(s0)
	lwu a4, 96(a3)
	sb a4, 32(s0)
	srli a5, a4, 8
	sb a5, 33(s0)
	srli a5, a4, 16
	sb a5, 34(s0)
	srli a5, a4, 24
	sb a5, 35(s0)
	lwu a4, 100(a3)
	sb a4, 36(s0)
	srli a5, a4, 8
	sb a5, 37(s0)
	srli a5, a4, 16
	sb a5, 38(s0)
	srli a5, a4, 24
	sb a5, 39(s0)
	lwu a4, 104(a3)
	sb a4, 40(s0)
	srli a5, a4, 8
	sb a5, 41(s0)
	srli a5, a4, 16
	sb a5, 42(s0)
	srli a5, a4, 24
	sb a5, 43(s0)
	lwu a4, 108(a3)
	sb a4, 44(s0)
	srli a5, a4, 8
	sb a5, 45(s0)
	srli a5, a4, 16
	sb a5, 46(s0)
	srli a5, a4, 24
	sb a5, 47(s0)
	lwu a4, 112(a3)
	sb a4, 48(s0)
	srli a5, a4, 8
	sb a5, 49(s0)
	srli a5, a4, 16
	sb a5, 50(s0)
	srli a5, a4, 24
	sb a5, 51(s0)
	lwu a4, 116(a3)
	sb a4, 52(s0)
	srli a5, a4, 8
	sb a5, 53(s0)
	srli a5, a4, 16
	sb a5, 54(s0)
	srli a5, a4, 24
	sb a5, 55(s0)
	lwu a4, 120(a3)
	sb a4, 56(s0)
	srli a5, a4, 8
	sb a5, 57(s0)
	srli a5, a4, 16
	sb a5, 58(s0)
	srli a5, a4, 24
	sb a5, 59(s0)
	lwu a4, 124(a3)
	sb a4, 60(s0)
	srli a5, a4, 8
	sb a5, 61(s0)
	srli a5, a4, 16
	sb a5, 62(s0)
	srli a5, a4, 24
	sb a5, 63(s0)
	lwu a4, 128(a3)
	sb a4, 64(s0)
	srli a5, a4, 8
	sb a5, 65(s0)
	srli a5, a4, 16
	sb a5, 66(s0)
	srli a5, a4, 24
	sb a5, 67(s0)
	lwu a4, 132(a3)
	sb a4, 68(s0)
	srli a5, a4, 8
	sb a5, 69(s0)
	srli a5, a4, 16
	sb a5, 70(s0)
	srli a5, a4, 24
	sb a5, 71(s0)
	lwu a4, 136(a3)
	sb a4, 72(s0)
	srli a5, a4, 8
	sb a5, 73(s0)
	srli a5, a4, 16
	sb a5, 74(s0)
	srli a5, a4, 24
	sb a5, 75(s0)
	lwu a4, 140(a3)
	sb a4, 76(s0)
	srli a5, a4, 8
	sb a5, 77(s0)
	srli a5, a4, 16
	sb a5, 78(s0)
	srli a5, a4, 24
	sb a5, 79(s0)
	lwu a4, 144(a3)
	sb a4, 80(s0)
	srli a5, a4, 8
	sb a5, 81(s0)
	srli a5, a4, 16
	sb a5, 82(s0)
	srli a5, a4, 24
	sb a5, 83(s0)
	lwu a4, 148(a3)
	sb a4, 84(s0)
	srli a5, a4, 8
	sb a5, 85(s0)
	srli a5, a4, 16
	sb a5, 86(s0)
	srli a5, a4, 24
	sb a5, 87(s0)
	lwu a4, 152(a3)
	sb a4, 88(s0)
	srli a5, a4, 8
	sb a5, 89(s0)
	srli a5, a4, 16
	sb a5, 90(s0)
	srli a5, a4, 24
	sb a5, 91(s0)
	lwu a4, 156(a3)
	sb a4, 92(s0)
	srli a5, a4, 8
	sb a5, 93(s0)
	srli a5, a4, 16
	sb a5, 94(s0)
	srli a5, a4, 24
	sb a5, 95(s0)
	lwu a4, 160(a3)
	sb a4, 96(s0)
	srli a5, a4, 8
	sb a5, 97(s0)
	srli a5, a4, 16
	sb a5, 98(s0)
	srli a5, a4, 24
	sb a5, 99(s0)
	lwu a4, 164(a3)
	sb a4, 100(s0)
	srli a5, a4, 8
	sb a5, 101(s0)
	srli a5, a4, 16
	sb a5, 102(s0)
	srli a5, a4, 24
	sb a5, 103(s0)
	lwu a4, 168(a3)
	sb a4, 104(s0)
	srli a5, a4, 8
	sb a5, 105(s0)
	srli a5, a4, 16
	sb a5, 106(s0)
	srli a5, a4, 24
	sb a5, 107(s0)
	lwu a4, 172(a3)
	sb a4, 108(s0)
	srli a5, a4, 8
	sb a5, 109(s0)
	srli a5, a4, 16
	sb a5, 110(s0)
	srli a5, a4, 24
	sb a5, 111(s0)
	lwu a4, 176(a3)
	sb a4, 112(s0)
	srli a5, a4, 8
	sb a5, 113(s0)
	srli a5, a4, 16
	sb a5, 114(s0)
	srli a5, a4, 24
	sb a5, 115(s0)
	lwu a4, 180(a3)
	sb a4, 116(s0)
	srli a5, a4, 8
	sb a5, 117(s0)
	srli a5, a4, 16
	sb a5, 118(s0)
	srli a5, a4, 24
	sb a5, 119(s0)
	lwu a4, 184(a3)
	sb a4, 120(s0)
	srli a5, a4, 8
	sb a5, 121(s0)
	srli a5, a4, 16
	sb a5, 122(s0)
	srli a5, a4, 24
	sb a5, 123(s0)
	lwu a4, 188(a3)
	sb a4, 124(s0)
	srli a5, a4, 8
	sb a5, 125(s0)
	srli a5, a4, 16
	sb a5, 126(s0)
	srli a5, a4, 24
	sb a5, 127(s0)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	addi s2, s2, 1
	addi a4, s2, -16
	bnez a4, 236b
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	slli a4, s6, 1
	add s0, s5, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	add a4, a4, a5
	slli a5, a4, 63
	srli a5, a5, 63
	sb a5, 32(a3)
	slli a5, a4, 62
	srli a5, a5, 63
	sb a5, 33(a3)
	slli a5, a4, 61
	srli a5, a5, 63
	sb a5, 34(a3)
	slli a5, a4, 60
	srli a5, a5, 63
	sb a5, 35(a3)
	slli a5, a4, 59
	srli a5, a5, 63
	sb a5, 36(a3)
	slli a5, a4, 58
	srli a5, a5, 63
	sb a5, 37(a3)
	slli a5, a4, 57
	srli a5, a5, 63
	sb a5, 38(a3)
	slli a5, a4, 56
	srli a5, a5, 63
	sb a5, 39(a3)
	slli a5, a4, 55
	srli a5, a5, 63
	sb a5, 40(a3)
	slli a5, a4, 54
	srli a5, a5, 63
	sb a5, 41(a3)
	slli a5, a4, 53
	srli a5, a5, 63
	sb a5, 42(a3)
	slli a5, a4, 52
	srli a5, a5, 63
	sb a5, 43(a3)
	slli a5, a4, 51
	srli a5, a5, 63
	sb a5, 44(a3)
	slli a5, a4, 50
	srli a5, a5, 63
	sb a5, 45(a3)
	slli a5, a4, 49
	srli a5, a5, 63
	sb a5, 46(a3)
	slli a5, a4, 48
	srli a5, a5, 63
	sb a5, 47(a3)
	addi s2, zero, 16
237:
	addi s2, s2, -1
	lwu a4, 64(a3)
	sw a4, 608(a3)
	lwu a4, 68(a3)
	sw a4, 612(a3)
	lwu a4, 72(a3)
	sw a4, 616(a3)
	lwu a4, 76(a3)
	sw a4, 620(a3)
	lwu a4, 80(a3)
	sw a4, 624(a3)
	lwu a4, 84(a3)
	sw a4, 628(a3)
	lwu a4, 88(a3)
	sw a4, 632(a3)
	lwu a4, 92(a3)
	sw a4, 636(a3)
	lwu a4, 96(a3)
	sw a4, 640(a3)
	lwu a4, 100(a3)
	sw a4, 644(a3)
	lwu a4, 104(a3)
	sw a4, 648(a3)
	lwu a4, 108(a3)
	sw a4, 652(a3)
	lwu a4, 112(a3)
	sw a4, 656(a3)
	lwu a4, 116(a3)
	sw a4, 660(a3)
	lwu a4, 120(a3)
	sw a4, 664(a3)
	lwu a4, 124(a3)
	sw a4, 668(a3)
	lwu a4, 128(a3)
	sw a4, 672(a3)
	lwu a4, 132(a3)
	sw a4, 676(a3)
	lwu a4, 136(a3)
	sw a4, 680(a3)
	lwu a4, 140(a3)
	sw a4, 684(a3)
	lwu a4, 144(a3)
	sw a4, 688(a3)
	lwu a4, 148(a3)
	sw a4, 692(a3)
	lwu a4, 152(a3)
	sw a4, 696(a3)
	lwu a4, 156(a3)
	sw a4, 700(a3)
	lwu a4, 160(a3)
	sw a4, 704(a3)
	lwu a4, 164(a3)
	sw a4, 708(a3)
	lwu a4, 168(a3)
	sw a4, 712(a3)
	lwu a4, 172(a3)
	sw a4, 716(a3)
	lwu a4, 176(a3)
	sw a4, 720(a3)
	lwu a4, 180(a3)
	sw a4, 724(a3)
	lwu a4, 184(a3)
	sw a4, 728(a3)
	lwu a4, 188(a3)
	sw a4, 732(a3)
	lui s0, 1
	addiw s0, s0, 1632
	add s0, a3, s0
	slli a4, s2, 7
	add s0, s0, a4
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lwu a4, 608(a3)
	sw a4, 64(a3)
	lwu a4, 612(a3)
	sw a4, 68(a3)
	lwu a4, 616(a3)
	sw a4, 72(a3)
	lwu a4, 620(a3)
	sw a4, 76(a3)
	lwu a4, 624(a3)
	sw a4, 80(a3)
	lwu a4, 628(a3)
	sw a4, 84(a3)
	lwu a4, 632(a3)
	sw a4, 88(a3)
	lwu a4, 636(a3)
	sw a4, 92(a3)
	lwu a4, 640(a3)
	sw a4, 96(a3)
	lwu a4, 644(a3)
	sw a4, 100(a3)
	lwu a4, 648(a3)
	sw a4, 104(a3)
	lwu a4, 652(a3)
	sw a4, 108(a3)
	lwu a4, 656(a3)
	sw a4, 112(a3)
	lwu a4, 660(a3)
	sw a4, 116(a3)
	lwu a4, 664(a3)
	sw a4, 120(a3)
	lwu a4, 668(a3)
	sw a4, 124(a3)
	lwu a4, 672(a3)
	sw a4, 128(a3)
	lwu a4, 676(a3)
	sw a4, 132(a3)
	lwu a4, 680(a3)
	sw a4, 136(a3)
	lwu a4, 684(a3)
	sw a4, 140(a3)
	lwu a4, 688(a3)
	sw a4, 144(a3)
	lwu a4, 692(a3)
	sw a4, 148(a3)
	lwu a4, 696(a3)
	sw a4, 152(a3)
	lwu a4, 700(a3)
	sw a4, 156(a3)
	lwu a4, 704(a3)
	sw a4, 160(a3)
	lwu a4, 708(a3)
	sw a4, 164(a3)
	lwu a4, 712(a3)
	sw a4, 168(a3)
	lwu a4, 716(a3)
	sw a4, 172(a3)
	lwu a4, 720(a3)
	sw a4, 176(a3)
	lwu a4, 724(a3)
	sw a4, 180(a3)
	lwu a4, 728(a3)
	sw a4, 184(a3)
	lwu a4, 732(a3)
	sw a4, 188(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	add a4, a3, s2
	lbu a4, 32(a4)
	addi t0, a4, -1
	lwu a2, 64(a3)
	lwu a4, 608(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 64(a3)
	sw a4, 608(a3)
	lwu a2, 68(a3)
	lwu a4, 612(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 68(a3)
	sw a4, 612(a3)
	lwu a2, 72(a3)
	lwu a4, 616(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 72(a3)
	sw a4, 616(a3)
	lwu a2, 76(a3)
	lwu a4, 620(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 76(a3)
	sw a4, 620(a3)
	lwu a2, 80(a3)
	lwu a4, 624(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 80(a3)
	sw a4, 624(a3)
	lwu a2, 84(a3)
	lwu a4, 628(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 84(a3)
	sw a4, 628(a3)
	lwu a2, 88(a3)
	lwu a4, 632(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 88(a3)
	sw a4, 632(a3)
	lwu a2, 92(a3)
	lwu a4, 636(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 92(a3)
	sw a4, 636(a3)
	lwu a2, 96(a3)
	lwu a4, 640(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 96(a3)
	sw a4, 640(a3)
	lwu a2, 100(a3)
	lwu a4, 644(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 100(a3)
	sw a4, 644(a3)
	lwu a2, 104(a3)
	lwu a4, 648(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 104(a3)
	sw a4, 648(a3)
	lwu a2, 108(a3)
	lwu a4, 652(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 108(a3)
	sw a4, 652(a3)
	lwu a2, 112(a3)
	lwu a4, 656(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 112(a3)
	sw a4, 656(a3)
	lwu a2, 116(a3)
	lwu a4, 660(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 116(a3)
	sw a4, 660(a3)
	lwu a2, 120(a3)
	lwu a4, 664(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 120(a3)
	sw a4, 664(a3)
	lwu a2, 124(a3)
	lwu a4, 668(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 124(a3)
	sw a4, 668(a3)
	lwu a2, 128(a3)
	lwu a4, 672(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 128(a3)
	sw a4, 672(a3)
	lwu a2, 132(a3)
	lwu a4, 676(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 132(a3)
	sw a4, 676(a3)
	lwu a2, 136(a3)
	lwu a4, 680(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 136(a3)
	sw a4, 680(a3)
	lwu a2, 140(a3)
	lwu a4, 684(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 140(a3)
	sw a4, 684(a3)
	lwu a2, 144(a3)
	lwu a4, 688(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 144(a3)
	sw a4, 688(a3)
	lwu a2, 148(a3)
	lwu a4, 692(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 148(a3)
	sw a4, 692(a3)
	lwu a2, 152(a3)
	lwu a4, 696(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 152(a3)
	sw a4, 696(a3)
	lwu a2, 156(a3)
	lwu a4, 700(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 156(a3)
	sw a4, 700(a3)
	lwu a2, 160(a3)
	lwu a4, 704(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 704(a3)
	lwu a2, 164(a3)
	lwu a4, 708(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 708(a3)
	lwu a2, 168(a3)
	lwu a4, 712(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 712(a3)
	lwu a2, 172(a3)
	lwu a4, 716(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 716(a3)
	lwu a2, 176(a3)
	lwu a4, 720(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 720(a3)
	lwu a2, 180(a3)
	lwu a4, 724(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 724(a3)
	lwu a2, 184(a3)
	lwu a4, 728(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 728(a3)
	lwu a2, 188(a3)
	lwu a4, 732(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 732(a3)
	bnez s2, 237b
	bnez s6, 235b
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lui s0, 2
	addiw s0, s0, -288
	add s0, a3, s0
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi a0, a3, 0
	call {vg_ed25519_r32_point_add}
	addi a3, a0, 0
	lwu a4, 64(a3)
	sw a4, 192(a3)
	lwu a4, 68(a3)
	sw a4, 196(a3)
	lwu a4, 72(a3)
	sw a4, 200(a3)
	lwu a4, 76(a3)
	sw a4, 204(a3)
	lwu a4, 80(a3)
	sw a4, 208(a3)
	lwu a4, 84(a3)
	sw a4, 212(a3)
	lwu a4, 88(a3)
	sw a4, 216(a3)
	lwu a4, 92(a3)
	sw a4, 220(a3)
	lwu a4, 96(a3)
	sw a4, 224(a3)
	lwu a4, 100(a3)
	sw a4, 228(a3)
	lwu a4, 104(a3)
	sw a4, 232(a3)
	lwu a4, 108(a3)
	sw a4, 236(a3)
	lwu a4, 112(a3)
	sw a4, 240(a3)
	lwu a4, 116(a3)
	sw a4, 244(a3)
	lwu a4, 120(a3)
	sw a4, 248(a3)
	lwu a4, 124(a3)
	sw a4, 252(a3)
	lwu a4, 128(a3)
	sw a4, 256(a3)
	lwu a4, 132(a3)
	sw a4, 260(a3)
	lwu a4, 136(a3)
	sw a4, 264(a3)
	lwu a4, 140(a3)
	sw a4, 268(a3)
	lwu a4, 144(a3)
	sw a4, 272(a3)
	lwu a4, 148(a3)
	sw a4, 276(a3)
	lwu a4, 152(a3)
	sw a4, 280(a3)
	lwu a4, 156(a3)
	sw a4, 284(a3)
	lwu a4, 160(a3)
	sw a4, 288(a3)
	lwu a4, 164(a3)
	sw a4, 292(a3)
	lwu a4, 168(a3)
	sw a4, 296(a3)
	lwu a4, 172(a3)
	sw a4, 300(a3)
	lwu a4, 176(a3)
	sw a4, 304(a3)
	lwu a4, 180(a3)
	sw a4, 308(a3)
	lwu a4, 184(a3)
	sw a4, 312(a3)
	lwu a4, 188(a3)
	sw a4, 316(a3)
	lui s0, 2
	addiw s0, s0, -160
	add s0, a3, s0
	lbu a4, 0(s0)
	lbu a5, 1(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 64(a3)
	lbu a4, 4(s0)
	lbu a5, 5(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 68(a3)
	lbu a4, 8(s0)
	lbu a5, 9(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 72(a3)
	lbu a4, 12(s0)
	lbu a5, 13(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 76(a3)
	lbu a4, 16(s0)
	lbu a5, 17(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 80(a3)
	lbu a4, 20(s0)
	lbu a5, 21(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 84(a3)
	lbu a4, 24(s0)
	lbu a5, 25(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 88(a3)
	lbu a4, 28(s0)
	lbu a5, 29(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 92(a3)
	lbu a4, 32(s0)
	lbu a5, 33(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 96(a3)
	lbu a4, 36(s0)
	lbu a5, 37(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 100(a3)
	lbu a4, 40(s0)
	lbu a5, 41(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 104(a3)
	lbu a4, 44(s0)
	lbu a5, 45(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 108(a3)
	lbu a4, 48(s0)
	lbu a5, 49(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 112(a3)
	lbu a4, 52(s0)
	lbu a5, 53(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 116(a3)
	lbu a4, 56(s0)
	lbu a5, 57(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 120(a3)
	lbu a4, 60(s0)
	lbu a5, 61(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 124(a3)
	lbu a4, 64(s0)
	lbu a5, 65(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 128(a3)
	lbu a4, 68(s0)
	lbu a5, 69(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 132(a3)
	lbu a4, 72(s0)
	lbu a5, 73(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 74(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 75(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 136(a3)
	lbu a4, 76(s0)
	lbu a5, 77(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 78(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 79(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 140(a3)
	lbu a4, 80(s0)
	lbu a5, 81(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 82(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 83(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 144(a3)
	lbu a4, 84(s0)
	lbu a5, 85(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 86(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 87(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 148(a3)
	lbu a4, 88(s0)
	lbu a5, 89(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 90(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 91(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 152(a3)
	lbu a4, 92(s0)
	lbu a5, 93(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 94(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 95(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 156(a3)
	lbu a4, 96(s0)
	lbu a5, 97(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 98(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 99(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 160(a3)
	lbu a4, 100(s0)
	lbu a5, 101(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 102(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 103(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 164(a3)
	lbu a4, 104(s0)
	lbu a5, 105(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 106(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 107(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 168(a3)
	lbu a4, 108(s0)
	lbu a5, 109(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 110(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 111(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 172(a3)
	lbu a4, 112(s0)
	lbu a5, 113(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 114(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 115(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 176(a3)
	lbu a4, 116(s0)
	lbu a5, 117(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 118(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 119(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 180(a3)
	lbu a4, 120(s0)
	lbu a5, 121(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 122(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 123(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 184(a3)
	lbu a4, 124(s0)
	lbu a5, 125(s0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 126(s0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 127(s0)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 188(a3)
	addi a0, a3, 0
	addi a1, zero, 320
	addi a2, zero, 64
	addi a3, zero, 256
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 352
	addi a2, zero, 192
	addi a3, zero, 128
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 384
	addi a2, zero, 96
	addi a3, zero, 256
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	addi a0, a3, 0
	addi a1, zero, 416
	addi a2, zero, 224
	addi a3, zero, 128
	call {vg_gf25519_r32_mul}
	addi a3, a0, 0
	ld t3, 320(a3)
	ld a7, 352(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 328(a3)
	ld a7, 360(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 336(a3)
	ld a7, 368(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 344(a3)
	ld a7, 376(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 736(a3)
	sd t4, 744(a3)
	sd t5, 752(a3)
	sd t6, 760(a3)
	lwu a4, 736(a3)
	sw a4, 864(a3)
	lwu a4, 740(a3)
	sw a4, 868(a3)
	lwu a4, 744(a3)
	sw a4, 872(a3)
	lwu a4, 748(a3)
	sw a4, 876(a3)
	lwu a4, 752(a3)
	sw a4, 880(a3)
	lwu a4, 756(a3)
	sw a4, 884(a3)
	lwu a4, 760(a3)
	sw a4, 888(a3)
	lwu a4, 764(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 238f
	addi s3, zero, 0
	j 239f
238:
	ld t3, 384(a3)
	ld a7, 416(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 392(a3)
	ld a7, 424(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 400(a3)
	ld a7, 432(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 408(a3)
	ld a7, 440(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 736(a3)
	sd t4, 744(a3)
	sd t5, 752(a3)
	sd t6, 760(a3)
	lwu a4, 736(a3)
	sw a4, 864(a3)
	lwu a4, 740(a3)
	sw a4, 868(a3)
	lwu a4, 744(a3)
	sw a4, 872(a3)
	lwu a4, 748(a3)
	sw a4, 876(a3)
	lwu a4, 752(a3)
	sw a4, 880(a3)
	lwu a4, 756(a3)
	sw a4, 884(a3)
	lwu a4, 760(a3)
	sw a4, 888(a3)
	lwu a4, 764(a3)
	sw a4, 892(a3)
	lwu a4, 892(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 892(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 864(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 868(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 872(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 876(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 880(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 884(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 888(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 892(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 864(a3)
	add a4, a4, a5
	sw a4, 896(a3)
	srli a5, a4, 32
	lwu a4, 868(a3)
	add a4, a4, a5
	sw a4, 900(a3)
	srli a5, a4, 32
	lwu a4, 872(a3)
	add a4, a4, a5
	sw a4, 904(a3)
	srli a5, a4, 32
	lwu a4, 876(a3)
	add a4, a4, a5
	sw a4, 908(a3)
	srli a5, a4, 32
	lwu a4, 880(a3)
	add a4, a4, a5
	sw a4, 912(a3)
	srli a5, a4, 32
	lwu a4, 884(a3)
	add a4, a4, a5
	sw a4, 916(a3)
	srli a5, a4, 32
	lwu a4, 888(a3)
	add a4, a4, a5
	sw a4, 920(a3)
	srli a5, a4, 32
	lwu a4, 892(a3)
	add a4, a4, a5
	sw a4, 924(a3)
	srli a5, a4, 32
	lwu a4, 924(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 924(a3)
	lwu a4, 864(a3)
	lwu a2, 896(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 864(a3)
	lwu a4, 868(a3)
	lwu a2, 900(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 868(a3)
	lwu a4, 872(a3)
	lwu a2, 904(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 872(a3)
	lwu a4, 876(a3)
	lwu a2, 908(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 876(a3)
	lwu a4, 880(a3)
	lwu a2, 912(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 880(a3)
	lwu a4, 884(a3)
	lwu a2, 916(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 884(a3)
	lwu a4, 888(a3)
	lwu a2, 920(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 888(a3)
	lwu a4, 892(a3)
	lwu a2, 924(a3)
	xor a2, a2, a4
	and a2, a2, t0
	xor a4, a4, a2
	sw a4, 892(a3)
	addi a2, zero, 0
	lwu a4, 864(a3)
	add a2, a2, a4
	lwu a4, 868(a3)
	add a2, a2, a4
	lwu a4, 872(a3)
	add a2, a2, a4
	lwu a4, 876(a3)
	add a2, a2, a4
	lwu a4, 880(a3)
	add a2, a2, a4
	lwu a4, 884(a3)
	add a2, a2, a4
	lwu a4, 888(a3)
	add a2, a2, a4
	lwu a4, 892(a3)
	add a2, a2, a4
	beqz a2, 240f
	addi s3, zero, 0
	j 241f
240:
	addi s3, zero, 1
241:
239:
227:
21:
	addi a0, s3, 0
	ld s0, 1024(a3)
	ld s1, 1032(a3)
	ld s2, 1040(a3)
	ld s3, 1048(a3)
	ld s4, 1056(a3)
	ld s5, 1064(a3)
	ld s6, 1072(a3)
	ld s7, 1080(a3)
	ld s8, 1088(a3)
	ld s9, 1096(a3)
	ld s10, 1104(a3)
	ld s11, 1112(a3)
	ld ra, 1120(a3)
	ret
	.option pop

vg_ed25519_verify:
	.option push
	.option arch, +m, +c
	addi sp, sp, -272
	addi a5, sp, 0
	sd s7, 224(a5)
	sd s8, 232(a5)
	sd s9, 240(a5)
	sd s10, 248(a5)
	sd ra, 256(a5)
	addi s7, a1, 0
	addi s8, a2, 0
	addi s9, a4, 0
	addi s10, a5, 0
	lbu a5, 0(a3)
	sb a5, 128(s10)
	lbu a5, 1(a3)
	sb a5, 129(s10)
	lbu a5, 2(a3)
	sb a5, 130(s10)
	lbu a5, 3(a3)
	sb a5, 131(s10)
	lbu a5, 4(a3)
	sb a5, 132(s10)
	lbu a5, 5(a3)
	sb a5, 133(s10)
	lbu a5, 6(a3)
	sb a5, 134(s10)
	lbu a5, 7(a3)
	sb a5, 135(s10)
	lbu a5, 8(a3)
	sb a5, 136(s10)
	lbu a5, 9(a3)
	sb a5, 137(s10)
	lbu a5, 10(a3)
	sb a5, 138(s10)
	lbu a5, 11(a3)
	sb a5, 139(s10)
	lbu a5, 12(a3)
	sb a5, 140(s10)
	lbu a5, 13(a3)
	sb a5, 141(s10)
	lbu a5, 14(a3)
	sb a5, 142(s10)
	lbu a5, 15(a3)
	sb a5, 143(s10)
	lbu a5, 16(a3)
	sb a5, 144(s10)
	lbu a5, 17(a3)
	sb a5, 145(s10)
	lbu a5, 18(a3)
	sb a5, 146(s10)
	lbu a5, 19(a3)
	sb a5, 147(s10)
	lbu a5, 20(a3)
	sb a5, 148(s10)
	lbu a5, 21(a3)
	sb a5, 149(s10)
	lbu a5, 22(a3)
	sb a5, 150(s10)
	lbu a5, 23(a3)
	sb a5, 151(s10)
	lbu a5, 24(a3)
	sb a5, 152(s10)
	lbu a5, 25(a3)
	sb a5, 153(s10)
	lbu a5, 26(a3)
	sb a5, 154(s10)
	lbu a5, 27(a3)
	sb a5, 155(s10)
	lbu a5, 28(a3)
	sb a5, 156(s10)
	lbu a5, 29(a3)
	sb a5, 157(s10)
	lbu a5, 30(a3)
	sb a5, 158(s10)
	lbu a5, 31(a3)
	sb a5, 159(s10)
	lbu a5, 32(a3)
	sb a5, 160(s10)
	lbu a5, 33(a3)
	sb a5, 161(s10)
	lbu a5, 34(a3)
	sb a5, 162(s10)
	lbu a5, 35(a3)
	sb a5, 163(s10)
	lbu a5, 36(a3)
	sb a5, 164(s10)
	lbu a5, 37(a3)
	sb a5, 165(s10)
	lbu a5, 38(a3)
	sb a5, 166(s10)
	lbu a5, 39(a3)
	sb a5, 167(s10)
	lbu a5, 40(a3)
	sb a5, 168(s10)
	lbu a5, 41(a3)
	sb a5, 169(s10)
	lbu a5, 42(a3)
	sb a5, 170(s10)
	lbu a5, 43(a3)
	sb a5, 171(s10)
	lbu a5, 44(a3)
	sb a5, 172(s10)
	lbu a5, 45(a3)
	sb a5, 173(s10)
	lbu a5, 46(a3)
	sb a5, 174(s10)
	lbu a5, 47(a3)
	sb a5, 175(s10)
	lbu a5, 48(a3)
	sb a5, 176(s10)
	lbu a5, 49(a3)
	sb a5, 177(s10)
	lbu a5, 50(a3)
	sb a5, 178(s10)
	lbu a5, 51(a3)
	sb a5, 179(s10)
	lbu a5, 52(a3)
	sb a5, 180(s10)
	lbu a5, 53(a3)
	sb a5, 181(s10)
	lbu a5, 54(a3)
	sb a5, 182(s10)
	lbu a5, 55(a3)
	sb a5, 183(s10)
	lbu a5, 56(a3)
	sb a5, 184(s10)
	lbu a5, 57(a3)
	sb a5, 185(s10)
	lbu a5, 58(a3)
	sb a5, 186(s10)
	lbu a5, 59(a3)
	sb a5, 187(s10)
	lbu a5, 60(a3)
	sb a5, 188(s10)
	lbu a5, 61(a3)
	sb a5, 189(s10)
	lbu a5, 62(a3)
	sb a5, 190(s10)
	lbu a5, 63(a3)
	sb a5, 191(s10)
	lbu a5, 0(a0)
	sb a5, 192(s10)
	lbu a5, 1(a0)
	sb a5, 193(s10)
	lbu a5, 2(a0)
	sb a5, 194(s10)
	lbu a5, 3(a0)
	sb a5, 195(s10)
	lbu a5, 4(a0)
	sb a5, 196(s10)
	lbu a5, 5(a0)
	sb a5, 197(s10)
	lbu a5, 6(a0)
	sb a5, 198(s10)
	lbu a5, 7(a0)
	sb a5, 199(s10)
	lbu a5, 8(a0)
	sb a5, 200(s10)
	lbu a5, 9(a0)
	sb a5, 201(s10)
	lbu a5, 10(a0)
	sb a5, 202(s10)
	lbu a5, 11(a0)
	sb a5, 203(s10)
	lbu a5, 12(a0)
	sb a5, 204(s10)
	lbu a5, 13(a0)
	sb a5, 205(s10)
	lbu a5, 14(a0)
	sb a5, 206(s10)
	lbu a5, 15(a0)
	sb a5, 207(s10)
	lbu a5, 16(a0)
	sb a5, 208(s10)
	lbu a5, 17(a0)
	sb a5, 209(s10)
	lbu a5, 18(a0)
	sb a5, 210(s10)
	lbu a5, 19(a0)
	sb a5, 211(s10)
	lbu a5, 20(a0)
	sb a5, 212(s10)
	lbu a5, 21(a0)
	sb a5, 213(s10)
	lbu a5, 22(a0)
	sb a5, 214(s10)
	lbu a5, 23(a0)
	sb a5, 215(s10)
	lbu a5, 24(a0)
	sb a5, 216(s10)
	lbu a5, 25(a0)
	sb a5, 217(s10)
	lbu a5, 26(a0)
	sb a5, 218(s10)
	lbu a5, 27(a0)
	sb a5, 219(s10)
	lbu a5, 28(a0)
	sb a5, 220(s10)
	lbu a5, 29(a0)
	sb a5, 221(s10)
	lbu a5, 30(a0)
	sb a5, 222(s10)
	lbu a5, 31(a0)
	sb a5, 223(s10)
	addi a0, s9, 0
	call {vg_sha512_init}
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s10, 128
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 32
	addi a2, s10, 192
	addi a3, zero, 32
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, zero, 64
	addi a2, s7, 0
	addi a3, s8, 0
	call {vg_sha512_update}
	addi a0, s9, 0
	addi a1, s8, 64
	addi a2, s10, 64
	call {vg_sha512_finalize}
	addi a0, s10, 0
	addi a1, s10, 64
	addi a2, s9, 0
	call {vg_ed25519_scalar_reduce}
	addi a5, zero, 0
	sd a5, 32(s10)
	sd a5, 40(s10)
	sd a5, 48(s10)
	sd a5, 56(s10)
	addi a0, s10, 192
	addi a1, s10, 128
	addi a2, s10, 0
	addi a3, s9, 0
	call {vg_ed25519_verify_equation}
	ld ra, 256(s10)
	ld s7, 224(s10)
	ld s8, 232(s10)
	ld s9, 240(s10)
	ld s10, 248(s10)
	addi sp, sp, 272
	ret
	.option pop
