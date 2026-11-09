// The functions of `src/x448.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_exchange:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	addi t0, sp, 0
	sd a0, 0(t0)
	call {vg_x448}
	addi t0, sp, 0
	ld t0, 0(t0)
	addi t1, zero, 0
	lbu t2, 0(t0)
	or t1, t1, t2
	lbu t2, 1(t0)
	or t1, t1, t2
	lbu t2, 2(t0)
	or t1, t1, t2
	lbu t2, 3(t0)
	or t1, t1, t2
	lbu t2, 4(t0)
	or t1, t1, t2
	lbu t2, 5(t0)
	or t1, t1, t2
	lbu t2, 6(t0)
	or t1, t1, t2
	lbu t2, 7(t0)
	or t1, t1, t2
	lbu t2, 8(t0)
	or t1, t1, t2
	lbu t2, 9(t0)
	or t1, t1, t2
	lbu t2, 10(t0)
	or t1, t1, t2
	lbu t2, 11(t0)
	or t1, t1, t2
	lbu t2, 12(t0)
	or t1, t1, t2
	lbu t2, 13(t0)
	or t1, t1, t2
	lbu t2, 14(t0)
	or t1, t1, t2
	lbu t2, 15(t0)
	or t1, t1, t2
	lbu t2, 16(t0)
	or t1, t1, t2
	lbu t2, 17(t0)
	or t1, t1, t2
	lbu t2, 18(t0)
	or t1, t1, t2
	lbu t2, 19(t0)
	or t1, t1, t2
	lbu t2, 20(t0)
	or t1, t1, t2
	lbu t2, 21(t0)
	or t1, t1, t2
	lbu t2, 22(t0)
	or t1, t1, t2
	lbu t2, 23(t0)
	or t1, t1, t2
	lbu t2, 24(t0)
	or t1, t1, t2
	lbu t2, 25(t0)
	or t1, t1, t2
	lbu t2, 26(t0)
	or t1, t1, t2
	lbu t2, 27(t0)
	or t1, t1, t2
	lbu t2, 28(t0)
	or t1, t1, t2
	lbu t2, 29(t0)
	or t1, t1, t2
	lbu t2, 30(t0)
	or t1, t1, t2
	lbu t2, 31(t0)
	or t1, t1, t2
	lbu t2, 32(t0)
	or t1, t1, t2
	lbu t2, 33(t0)
	or t1, t1, t2
	lbu t2, 34(t0)
	or t1, t1, t2
	lbu t2, 35(t0)
	or t1, t1, t2
	lbu t2, 36(t0)
	or t1, t1, t2
	lbu t2, 37(t0)
	or t1, t1, t2
	lbu t2, 38(t0)
	or t1, t1, t2
	lbu t2, 39(t0)
	or t1, t1, t2
	lbu t2, 40(t0)
	or t1, t1, t2
	lbu t2, 41(t0)
	or t1, t1, t2
	lbu t2, 42(t0)
	or t1, t1, t2
	lbu t2, 43(t0)
	or t1, t1, t2
	lbu t2, 44(t0)
	or t1, t1, t2
	lbu t2, 45(t0)
	or t1, t1, t2
	lbu t2, 46(t0)
	or t1, t1, t2
	lbu t2, 47(t0)
	or t1, t1, t2
	lbu t2, 48(t0)
	or t1, t1, t2
	lbu t2, 49(t0)
	or t1, t1, t2
	lbu t2, 50(t0)
	or t1, t1, t2
	lbu t2, 51(t0)
	or t1, t1, t2
	lbu t2, 52(t0)
	or t1, t1, t2
	lbu t2, 53(t0)
	or t1, t1, t2
	lbu t2, 54(t0)
	or t1, t1, t2
	lbu t2, 55(t0)
	or t1, t1, t2
	addi t2, zero, 0
	sltu a0, t2, t1
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop

vg_x448_base:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi a4, zero, 5
	addi a5, zero, 0
	sw a4, 0(a3)
	sw a4, 168(a3)
	sw a5, 4(a3)
	sw a5, 8(a3)
	sw a5, 12(a3)
	sw a5, 16(a3)
	sw a5, 20(a3)
	sw a5, 24(a3)
	sw a5, 28(a3)
	sw a5, 32(a3)
	sw a5, 36(a3)
	sw a5, 40(a3)
	sw a5, 44(a3)
	sw a5, 48(a3)
	sw a5, 52(a3)
	sw a5, 172(a3)
	sw a5, 176(a3)
	sw a5, 180(a3)
	sw a5, 184(a3)
	sw a5, 188(a3)
	sw a5, 192(a3)
	sw a5, 196(a3)
	sw a5, 200(a3)
	sw a5, 204(a3)
	sw a5, 208(a3)
	sw a5, 212(a3)
	sw a5, 216(a3)
	sw a5, 220(a3)
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
