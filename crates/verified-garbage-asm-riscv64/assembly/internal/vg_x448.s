// The functions of `src/internal/vg_x448.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
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
	sw a4, 0(a3)
	sw a4, 168(a3)
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
	sw a4, 4(a3)
	sw a4, 172(a3)
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
	sw a4, 8(a3)
	sw a4, 176(a3)
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
	sw a4, 12(a3)
	sw a4, 180(a3)
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
	sw a4, 16(a3)
	sw a4, 184(a3)
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
	sw a4, 20(a3)
	sw a4, 188(a3)
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
	sw a4, 24(a3)
	sw a4, 192(a3)
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
	sw a4, 28(a3)
	sw a4, 196(a3)
	lbu a4, 32(a2)
	lbu a5, 33(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 32(a3)
	sw a4, 200(a3)
	lbu a4, 36(a2)
	lbu a5, 37(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 36(a3)
	sw a4, 204(a3)
	lbu a4, 40(a2)
	lbu a5, 41(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 40(a3)
	sw a4, 208(a3)
	lbu a4, 44(a2)
	lbu a5, 45(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 44(a3)
	sw a4, 212(a3)
	lbu a4, 48(a2)
	lbu a5, 49(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 48(a3)
	sw a4, 216(a3)
	lbu a4, 52(a2)
	lbu a5, 53(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 52(a3)
	sw a4, 220(a3)
	addi a4, zero, 1
	addi a5, zero, 0
	lui a2, 10
	addiw a2, a2, -1879
	sw a4, 56(a3)
	sw a5, 112(a3)
	sw a4, 224(a3)
	sw a2, 784(a3)
	sw a5, 60(a3)
	sw a5, 64(a3)
	sw a5, 68(a3)
	sw a5, 72(a3)
	sw a5, 76(a3)
	sw a5, 80(a3)
	sw a5, 84(a3)
	sw a5, 88(a3)
	sw a5, 92(a3)
	sw a5, 96(a3)
	sw a5, 100(a3)
	sw a5, 104(a3)
	sw a5, 108(a3)
	sw a5, 116(a3)
	sw a5, 120(a3)
	sw a5, 124(a3)
	sw a5, 128(a3)
	sw a5, 132(a3)
	sw a5, 136(a3)
	sw a5, 140(a3)
	sw a5, 144(a3)
	sw a5, 148(a3)
	sw a5, 152(a3)
	sw a5, 156(a3)
	sw a5, 160(a3)
	sw a5, 164(a3)
	sw a5, 228(a3)
	sw a5, 232(a3)
	sw a5, 236(a3)
	sw a5, 240(a3)
	sw a5, 244(a3)
	sw a5, 248(a3)
	sw a5, 252(a3)
	sw a5, 256(a3)
	sw a5, 260(a3)
	sw a5, 264(a3)
	sw a5, 268(a3)
	sw a5, 272(a3)
	sw a5, 276(a3)
	sw a5, 788(a3)
	sw a5, 792(a3)
	sw a5, 796(a3)
	sw a5, 800(a3)
	sw a5, 804(a3)
	sw a5, 808(a3)
	sw a5, 812(a3)
	sw a5, 816(a3)
	sw a5, 820(a3)
	sw a5, 824(a3)
	sw a5, 828(a3)
	sw a5, 832(a3)
	sw a5, 836(a3)
	sd ra, 2040(a3)
	call {vg_x448_tail}
	ld ra, 2040(a3)
	ret
	.option pop
