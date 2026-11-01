// The functions of `src/rc4.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc4_init:
	.option push
	.option arch, +m, +c
	addi t2, a1, -1
	srli t2, t2, 8
	bnez t2, 20f
	addi sp, sp, -256
	addi a7, sp, 0
	addi a3, zero, 0
22:
	add t2, a7, a3
	sb a3, 0(t2)
	addi a3, a3, 1
	addi t2, zero, 256
	sub t2, a3, t2
	bnez t2, 22b
	addi a3, zero, 0
	addi t3, zero, 0
	addi a4, zero, 0
	addi t6, zero, 0
23:
	add t2, a7, a3
	lbu t0, 0(t2)
	add a4, a4, t0
	add t2, a0, t3
	lbu t0, 0(t2)
	add a4, a4, t0
	slli a4, a4, 56
	srli a4, a4, 56
	srli t5, a4, 3
	addi t2, zero, 1
	sll t5, t2, t5
	slli t2, t5, 63
	srai t2, t2, 63
	ld t1, 0(a7)
	and t1, t1, t2
	slli t2, t5, 62
	srai t2, t2, 63
	ld t0, 8(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 61
	srai t2, t2, 63
	ld t0, 16(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 60
	srai t2, t2, 63
	ld t0, 24(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 59
	srai t2, t2, 63
	ld t0, 32(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 58
	srai t2, t2, 63
	ld t0, 40(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 57
	srai t2, t2, 63
	ld t0, 48(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 56
	srai t2, t2, 63
	ld t0, 56(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 55
	srai t2, t2, 63
	ld t0, 64(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 54
	srai t2, t2, 63
	ld t0, 72(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 53
	srai t2, t2, 63
	ld t0, 80(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 52
	srai t2, t2, 63
	ld t0, 88(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 51
	srai t2, t2, 63
	ld t0, 96(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 50
	srai t2, t2, 63
	ld t0, 104(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 49
	srai t2, t2, 63
	ld t0, 112(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 48
	srai t2, t2, 63
	ld t0, 120(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 47
	srai t2, t2, 63
	ld t0, 128(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 46
	srai t2, t2, 63
	ld t0, 136(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 45
	srai t2, t2, 63
	ld t0, 144(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 44
	srai t2, t2, 63
	ld t0, 152(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 43
	srai t2, t2, 63
	ld t0, 160(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 42
	srai t2, t2, 63
	ld t0, 168(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 41
	srai t2, t2, 63
	ld t0, 176(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 40
	srai t2, t2, 63
	ld t0, 184(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 39
	srai t2, t2, 63
	ld t0, 192(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 38
	srai t2, t2, 63
	ld t0, 200(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 37
	srai t2, t2, 63
	ld t0, 208(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 36
	srai t2, t2, 63
	ld t0, 216(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 35
	srai t2, t2, 63
	ld t0, 224(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 34
	srai t2, t2, 63
	ld t0, 232(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 33
	srai t2, t2, 63
	ld t0, 240(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 32
	srai t2, t2, 63
	ld t0, 248(a7)
	and t0, t0, t2
	or t1, t1, t0
	andi t2, a4, 7
	slli t2, t2, 3
	srl a5, t1, t2
	andi a5, a5, 255
	add t2, a7, a3
	lbu t0, 0(t2)
	xor a5, a5, t0
	andi t2, a4, 7
	slli t2, t2, 3
	sll t1, a5, t2
	add t2, a7, a3
	lbu t0, 0(t2)
	xor a5, a5, t0
	slli t2, t5, 63
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 0(a7)
	xor t0, t0, t2
	sd t0, 0(a7)
	slli t2, t5, 62
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 8(a7)
	xor t0, t0, t2
	sd t0, 8(a7)
	slli t2, t5, 61
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 16(a7)
	xor t0, t0, t2
	sd t0, 16(a7)
	slli t2, t5, 60
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 24(a7)
	xor t0, t0, t2
	sd t0, 24(a7)
	slli t2, t5, 59
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 32(a7)
	xor t0, t0, t2
	sd t0, 32(a7)
	slli t2, t5, 58
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 40(a7)
	xor t0, t0, t2
	sd t0, 40(a7)
	slli t2, t5, 57
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 48(a7)
	xor t0, t0, t2
	sd t0, 48(a7)
	slli t2, t5, 56
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 56(a7)
	xor t0, t0, t2
	sd t0, 56(a7)
	slli t2, t5, 55
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 64(a7)
	xor t0, t0, t2
	sd t0, 64(a7)
	slli t2, t5, 54
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 72(a7)
	xor t0, t0, t2
	sd t0, 72(a7)
	slli t2, t5, 53
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 80(a7)
	xor t0, t0, t2
	sd t0, 80(a7)
	slli t2, t5, 52
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 88(a7)
	xor t0, t0, t2
	sd t0, 88(a7)
	slli t2, t5, 51
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 96(a7)
	xor t0, t0, t2
	sd t0, 96(a7)
	slli t2, t5, 50
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 104(a7)
	xor t0, t0, t2
	sd t0, 104(a7)
	slli t2, t5, 49
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 112(a7)
	xor t0, t0, t2
	sd t0, 112(a7)
	slli t2, t5, 48
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 120(a7)
	xor t0, t0, t2
	sd t0, 120(a7)
	slli t2, t5, 47
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 128(a7)
	xor t0, t0, t2
	sd t0, 128(a7)
	slli t2, t5, 46
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 136(a7)
	xor t0, t0, t2
	sd t0, 136(a7)
	slli t2, t5, 45
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 144(a7)
	xor t0, t0, t2
	sd t0, 144(a7)
	slli t2, t5, 44
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 152(a7)
	xor t0, t0, t2
	sd t0, 152(a7)
	slli t2, t5, 43
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 160(a7)
	xor t0, t0, t2
	sd t0, 160(a7)
	slli t2, t5, 42
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 168(a7)
	xor t0, t0, t2
	sd t0, 168(a7)
	slli t2, t5, 41
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 176(a7)
	xor t0, t0, t2
	sd t0, 176(a7)
	slli t2, t5, 40
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 184(a7)
	xor t0, t0, t2
	sd t0, 184(a7)
	slli t2, t5, 39
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 192(a7)
	xor t0, t0, t2
	sd t0, 192(a7)
	slli t2, t5, 38
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 200(a7)
	xor t0, t0, t2
	sd t0, 200(a7)
	slli t2, t5, 37
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 208(a7)
	xor t0, t0, t2
	sd t0, 208(a7)
	slli t2, t5, 36
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 216(a7)
	xor t0, t0, t2
	sd t0, 216(a7)
	slli t2, t5, 35
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 224(a7)
	xor t0, t0, t2
	sd t0, 224(a7)
	slli t2, t5, 34
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 232(a7)
	xor t0, t0, t2
	sd t0, 232(a7)
	slli t2, t5, 33
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 240(a7)
	xor t0, t0, t2
	sd t0, 240(a7)
	slli t2, t5, 32
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 248(a7)
	xor t0, t0, t2
	sd t0, 248(a7)
	add t2, a7, a3
	sb a5, 0(t2)
	addi t3, t3, 1
	sub t2, t3, a1
	addi t0, t2, -1
	xor t0, t0, t2
	srli t2, t0, 63
	addi t2, t2, -1
	and t3, t3, t2
	addi a3, a3, 1
	addi t2, zero, 256
	sub t2, a3, t2
	bnez t2, 23b
	lbu t0, 0(a7)
	sb t0, 0(a2)
	lbu t0, 1(a7)
	sb t0, 1(a2)
	lbu t0, 2(a7)
	sb t0, 2(a2)
	lbu t0, 3(a7)
	sb t0, 3(a2)
	lbu t0, 4(a7)
	sb t0, 4(a2)
	lbu t0, 5(a7)
	sb t0, 5(a2)
	lbu t0, 6(a7)
	sb t0, 6(a2)
	lbu t0, 7(a7)
	sb t0, 7(a2)
	lbu t0, 8(a7)
	sb t0, 8(a2)
	lbu t0, 9(a7)
	sb t0, 9(a2)
	lbu t0, 10(a7)
	sb t0, 10(a2)
	lbu t0, 11(a7)
	sb t0, 11(a2)
	lbu t0, 12(a7)
	sb t0, 12(a2)
	lbu t0, 13(a7)
	sb t0, 13(a2)
	lbu t0, 14(a7)
	sb t0, 14(a2)
	lbu t0, 15(a7)
	sb t0, 15(a2)
	lbu t0, 16(a7)
	sb t0, 16(a2)
	lbu t0, 17(a7)
	sb t0, 17(a2)
	lbu t0, 18(a7)
	sb t0, 18(a2)
	lbu t0, 19(a7)
	sb t0, 19(a2)
	lbu t0, 20(a7)
	sb t0, 20(a2)
	lbu t0, 21(a7)
	sb t0, 21(a2)
	lbu t0, 22(a7)
	sb t0, 22(a2)
	lbu t0, 23(a7)
	sb t0, 23(a2)
	lbu t0, 24(a7)
	sb t0, 24(a2)
	lbu t0, 25(a7)
	sb t0, 25(a2)
	lbu t0, 26(a7)
	sb t0, 26(a2)
	lbu t0, 27(a7)
	sb t0, 27(a2)
	lbu t0, 28(a7)
	sb t0, 28(a2)
	lbu t0, 29(a7)
	sb t0, 29(a2)
	lbu t0, 30(a7)
	sb t0, 30(a2)
	lbu t0, 31(a7)
	sb t0, 31(a2)
	lbu t0, 32(a7)
	sb t0, 32(a2)
	lbu t0, 33(a7)
	sb t0, 33(a2)
	lbu t0, 34(a7)
	sb t0, 34(a2)
	lbu t0, 35(a7)
	sb t0, 35(a2)
	lbu t0, 36(a7)
	sb t0, 36(a2)
	lbu t0, 37(a7)
	sb t0, 37(a2)
	lbu t0, 38(a7)
	sb t0, 38(a2)
	lbu t0, 39(a7)
	sb t0, 39(a2)
	lbu t0, 40(a7)
	sb t0, 40(a2)
	lbu t0, 41(a7)
	sb t0, 41(a2)
	lbu t0, 42(a7)
	sb t0, 42(a2)
	lbu t0, 43(a7)
	sb t0, 43(a2)
	lbu t0, 44(a7)
	sb t0, 44(a2)
	lbu t0, 45(a7)
	sb t0, 45(a2)
	lbu t0, 46(a7)
	sb t0, 46(a2)
	lbu t0, 47(a7)
	sb t0, 47(a2)
	lbu t0, 48(a7)
	sb t0, 48(a2)
	lbu t0, 49(a7)
	sb t0, 49(a2)
	lbu t0, 50(a7)
	sb t0, 50(a2)
	lbu t0, 51(a7)
	sb t0, 51(a2)
	lbu t0, 52(a7)
	sb t0, 52(a2)
	lbu t0, 53(a7)
	sb t0, 53(a2)
	lbu t0, 54(a7)
	sb t0, 54(a2)
	lbu t0, 55(a7)
	sb t0, 55(a2)
	lbu t0, 56(a7)
	sb t0, 56(a2)
	lbu t0, 57(a7)
	sb t0, 57(a2)
	lbu t0, 58(a7)
	sb t0, 58(a2)
	lbu t0, 59(a7)
	sb t0, 59(a2)
	lbu t0, 60(a7)
	sb t0, 60(a2)
	lbu t0, 61(a7)
	sb t0, 61(a2)
	lbu t0, 62(a7)
	sb t0, 62(a2)
	lbu t0, 63(a7)
	sb t0, 63(a2)
	lbu t0, 64(a7)
	sb t0, 64(a2)
	lbu t0, 65(a7)
	sb t0, 65(a2)
	lbu t0, 66(a7)
	sb t0, 66(a2)
	lbu t0, 67(a7)
	sb t0, 67(a2)
	lbu t0, 68(a7)
	sb t0, 68(a2)
	lbu t0, 69(a7)
	sb t0, 69(a2)
	lbu t0, 70(a7)
	sb t0, 70(a2)
	lbu t0, 71(a7)
	sb t0, 71(a2)
	lbu t0, 72(a7)
	sb t0, 72(a2)
	lbu t0, 73(a7)
	sb t0, 73(a2)
	lbu t0, 74(a7)
	sb t0, 74(a2)
	lbu t0, 75(a7)
	sb t0, 75(a2)
	lbu t0, 76(a7)
	sb t0, 76(a2)
	lbu t0, 77(a7)
	sb t0, 77(a2)
	lbu t0, 78(a7)
	sb t0, 78(a2)
	lbu t0, 79(a7)
	sb t0, 79(a2)
	lbu t0, 80(a7)
	sb t0, 80(a2)
	lbu t0, 81(a7)
	sb t0, 81(a2)
	lbu t0, 82(a7)
	sb t0, 82(a2)
	lbu t0, 83(a7)
	sb t0, 83(a2)
	lbu t0, 84(a7)
	sb t0, 84(a2)
	lbu t0, 85(a7)
	sb t0, 85(a2)
	lbu t0, 86(a7)
	sb t0, 86(a2)
	lbu t0, 87(a7)
	sb t0, 87(a2)
	lbu t0, 88(a7)
	sb t0, 88(a2)
	lbu t0, 89(a7)
	sb t0, 89(a2)
	lbu t0, 90(a7)
	sb t0, 90(a2)
	lbu t0, 91(a7)
	sb t0, 91(a2)
	lbu t0, 92(a7)
	sb t0, 92(a2)
	lbu t0, 93(a7)
	sb t0, 93(a2)
	lbu t0, 94(a7)
	sb t0, 94(a2)
	lbu t0, 95(a7)
	sb t0, 95(a2)
	lbu t0, 96(a7)
	sb t0, 96(a2)
	lbu t0, 97(a7)
	sb t0, 97(a2)
	lbu t0, 98(a7)
	sb t0, 98(a2)
	lbu t0, 99(a7)
	sb t0, 99(a2)
	lbu t0, 100(a7)
	sb t0, 100(a2)
	lbu t0, 101(a7)
	sb t0, 101(a2)
	lbu t0, 102(a7)
	sb t0, 102(a2)
	lbu t0, 103(a7)
	sb t0, 103(a2)
	lbu t0, 104(a7)
	sb t0, 104(a2)
	lbu t0, 105(a7)
	sb t0, 105(a2)
	lbu t0, 106(a7)
	sb t0, 106(a2)
	lbu t0, 107(a7)
	sb t0, 107(a2)
	lbu t0, 108(a7)
	sb t0, 108(a2)
	lbu t0, 109(a7)
	sb t0, 109(a2)
	lbu t0, 110(a7)
	sb t0, 110(a2)
	lbu t0, 111(a7)
	sb t0, 111(a2)
	lbu t0, 112(a7)
	sb t0, 112(a2)
	lbu t0, 113(a7)
	sb t0, 113(a2)
	lbu t0, 114(a7)
	sb t0, 114(a2)
	lbu t0, 115(a7)
	sb t0, 115(a2)
	lbu t0, 116(a7)
	sb t0, 116(a2)
	lbu t0, 117(a7)
	sb t0, 117(a2)
	lbu t0, 118(a7)
	sb t0, 118(a2)
	lbu t0, 119(a7)
	sb t0, 119(a2)
	lbu t0, 120(a7)
	sb t0, 120(a2)
	lbu t0, 121(a7)
	sb t0, 121(a2)
	lbu t0, 122(a7)
	sb t0, 122(a2)
	lbu t0, 123(a7)
	sb t0, 123(a2)
	lbu t0, 124(a7)
	sb t0, 124(a2)
	lbu t0, 125(a7)
	sb t0, 125(a2)
	lbu t0, 126(a7)
	sb t0, 126(a2)
	lbu t0, 127(a7)
	sb t0, 127(a2)
	lbu t0, 128(a7)
	sb t0, 128(a2)
	lbu t0, 129(a7)
	sb t0, 129(a2)
	lbu t0, 130(a7)
	sb t0, 130(a2)
	lbu t0, 131(a7)
	sb t0, 131(a2)
	lbu t0, 132(a7)
	sb t0, 132(a2)
	lbu t0, 133(a7)
	sb t0, 133(a2)
	lbu t0, 134(a7)
	sb t0, 134(a2)
	lbu t0, 135(a7)
	sb t0, 135(a2)
	lbu t0, 136(a7)
	sb t0, 136(a2)
	lbu t0, 137(a7)
	sb t0, 137(a2)
	lbu t0, 138(a7)
	sb t0, 138(a2)
	lbu t0, 139(a7)
	sb t0, 139(a2)
	lbu t0, 140(a7)
	sb t0, 140(a2)
	lbu t0, 141(a7)
	sb t0, 141(a2)
	lbu t0, 142(a7)
	sb t0, 142(a2)
	lbu t0, 143(a7)
	sb t0, 143(a2)
	lbu t0, 144(a7)
	sb t0, 144(a2)
	lbu t0, 145(a7)
	sb t0, 145(a2)
	lbu t0, 146(a7)
	sb t0, 146(a2)
	lbu t0, 147(a7)
	sb t0, 147(a2)
	lbu t0, 148(a7)
	sb t0, 148(a2)
	lbu t0, 149(a7)
	sb t0, 149(a2)
	lbu t0, 150(a7)
	sb t0, 150(a2)
	lbu t0, 151(a7)
	sb t0, 151(a2)
	lbu t0, 152(a7)
	sb t0, 152(a2)
	lbu t0, 153(a7)
	sb t0, 153(a2)
	lbu t0, 154(a7)
	sb t0, 154(a2)
	lbu t0, 155(a7)
	sb t0, 155(a2)
	lbu t0, 156(a7)
	sb t0, 156(a2)
	lbu t0, 157(a7)
	sb t0, 157(a2)
	lbu t0, 158(a7)
	sb t0, 158(a2)
	lbu t0, 159(a7)
	sb t0, 159(a2)
	lbu t0, 160(a7)
	sb t0, 160(a2)
	lbu t0, 161(a7)
	sb t0, 161(a2)
	lbu t0, 162(a7)
	sb t0, 162(a2)
	lbu t0, 163(a7)
	sb t0, 163(a2)
	lbu t0, 164(a7)
	sb t0, 164(a2)
	lbu t0, 165(a7)
	sb t0, 165(a2)
	lbu t0, 166(a7)
	sb t0, 166(a2)
	lbu t0, 167(a7)
	sb t0, 167(a2)
	lbu t0, 168(a7)
	sb t0, 168(a2)
	lbu t0, 169(a7)
	sb t0, 169(a2)
	lbu t0, 170(a7)
	sb t0, 170(a2)
	lbu t0, 171(a7)
	sb t0, 171(a2)
	lbu t0, 172(a7)
	sb t0, 172(a2)
	lbu t0, 173(a7)
	sb t0, 173(a2)
	lbu t0, 174(a7)
	sb t0, 174(a2)
	lbu t0, 175(a7)
	sb t0, 175(a2)
	lbu t0, 176(a7)
	sb t0, 176(a2)
	lbu t0, 177(a7)
	sb t0, 177(a2)
	lbu t0, 178(a7)
	sb t0, 178(a2)
	lbu t0, 179(a7)
	sb t0, 179(a2)
	lbu t0, 180(a7)
	sb t0, 180(a2)
	lbu t0, 181(a7)
	sb t0, 181(a2)
	lbu t0, 182(a7)
	sb t0, 182(a2)
	lbu t0, 183(a7)
	sb t0, 183(a2)
	lbu t0, 184(a7)
	sb t0, 184(a2)
	lbu t0, 185(a7)
	sb t0, 185(a2)
	lbu t0, 186(a7)
	sb t0, 186(a2)
	lbu t0, 187(a7)
	sb t0, 187(a2)
	lbu t0, 188(a7)
	sb t0, 188(a2)
	lbu t0, 189(a7)
	sb t0, 189(a2)
	lbu t0, 190(a7)
	sb t0, 190(a2)
	lbu t0, 191(a7)
	sb t0, 191(a2)
	lbu t0, 192(a7)
	sb t0, 192(a2)
	lbu t0, 193(a7)
	sb t0, 193(a2)
	lbu t0, 194(a7)
	sb t0, 194(a2)
	lbu t0, 195(a7)
	sb t0, 195(a2)
	lbu t0, 196(a7)
	sb t0, 196(a2)
	lbu t0, 197(a7)
	sb t0, 197(a2)
	lbu t0, 198(a7)
	sb t0, 198(a2)
	lbu t0, 199(a7)
	sb t0, 199(a2)
	lbu t0, 200(a7)
	sb t0, 200(a2)
	lbu t0, 201(a7)
	sb t0, 201(a2)
	lbu t0, 202(a7)
	sb t0, 202(a2)
	lbu t0, 203(a7)
	sb t0, 203(a2)
	lbu t0, 204(a7)
	sb t0, 204(a2)
	lbu t0, 205(a7)
	sb t0, 205(a2)
	lbu t0, 206(a7)
	sb t0, 206(a2)
	lbu t0, 207(a7)
	sb t0, 207(a2)
	lbu t0, 208(a7)
	sb t0, 208(a2)
	lbu t0, 209(a7)
	sb t0, 209(a2)
	lbu t0, 210(a7)
	sb t0, 210(a2)
	lbu t0, 211(a7)
	sb t0, 211(a2)
	lbu t0, 212(a7)
	sb t0, 212(a2)
	lbu t0, 213(a7)
	sb t0, 213(a2)
	lbu t0, 214(a7)
	sb t0, 214(a2)
	lbu t0, 215(a7)
	sb t0, 215(a2)
	lbu t0, 216(a7)
	sb t0, 216(a2)
	lbu t0, 217(a7)
	sb t0, 217(a2)
	lbu t0, 218(a7)
	sb t0, 218(a2)
	lbu t0, 219(a7)
	sb t0, 219(a2)
	lbu t0, 220(a7)
	sb t0, 220(a2)
	lbu t0, 221(a7)
	sb t0, 221(a2)
	lbu t0, 222(a7)
	sb t0, 222(a2)
	lbu t0, 223(a7)
	sb t0, 223(a2)
	lbu t0, 224(a7)
	sb t0, 224(a2)
	lbu t0, 225(a7)
	sb t0, 225(a2)
	lbu t0, 226(a7)
	sb t0, 226(a2)
	lbu t0, 227(a7)
	sb t0, 227(a2)
	lbu t0, 228(a7)
	sb t0, 228(a2)
	lbu t0, 229(a7)
	sb t0, 229(a2)
	lbu t0, 230(a7)
	sb t0, 230(a2)
	lbu t0, 231(a7)
	sb t0, 231(a2)
	lbu t0, 232(a7)
	sb t0, 232(a2)
	lbu t0, 233(a7)
	sb t0, 233(a2)
	lbu t0, 234(a7)
	sb t0, 234(a2)
	lbu t0, 235(a7)
	sb t0, 235(a2)
	lbu t0, 236(a7)
	sb t0, 236(a2)
	lbu t0, 237(a7)
	sb t0, 237(a2)
	lbu t0, 238(a7)
	sb t0, 238(a2)
	lbu t0, 239(a7)
	sb t0, 239(a2)
	lbu t0, 240(a7)
	sb t0, 240(a2)
	lbu t0, 241(a7)
	sb t0, 241(a2)
	lbu t0, 242(a7)
	sb t0, 242(a2)
	lbu t0, 243(a7)
	sb t0, 243(a2)
	lbu t0, 244(a7)
	sb t0, 244(a2)
	lbu t0, 245(a7)
	sb t0, 245(a2)
	lbu t0, 246(a7)
	sb t0, 246(a2)
	lbu t0, 247(a7)
	sb t0, 247(a2)
	lbu t0, 248(a7)
	sb t0, 248(a2)
	lbu t0, 249(a7)
	sb t0, 249(a2)
	lbu t0, 250(a7)
	sb t0, 250(a2)
	lbu t0, 251(a7)
	sb t0, 251(a2)
	lbu t0, 252(a7)
	sb t0, 252(a2)
	lbu t0, 253(a7)
	sb t0, 253(a2)
	lbu t0, 254(a7)
	sb t0, 254(a2)
	lbu t0, 255(a7)
	sb t0, 255(a2)
	addi t2, zero, 0
	sb t2, 256(a2)
	sb t2, 257(a2)
	addi a0, zero, 0
	sd t6, 0(a7)
	sd t6, 8(a7)
	sd t6, 16(a7)
	sd t6, 24(a7)
	sd t6, 32(a7)
	sd t6, 40(a7)
	sd t6, 48(a7)
	sd t6, 56(a7)
	sd t6, 64(a7)
	sd t6, 72(a7)
	sd t6, 80(a7)
	sd t6, 88(a7)
	sd t6, 96(a7)
	sd t6, 104(a7)
	sd t6, 112(a7)
	sd t6, 120(a7)
	sd t6, 128(a7)
	sd t6, 136(a7)
	sd t6, 144(a7)
	sd t6, 152(a7)
	sd t6, 160(a7)
	sd t6, 168(a7)
	sd t6, 176(a7)
	sd t6, 184(a7)
	sd t6, 192(a7)
	sd t6, 200(a7)
	sd t6, 208(a7)
	sd t6, 216(a7)
	sd t6, 224(a7)
	sd t6, 232(a7)
	sd t6, 240(a7)
	sd t6, 248(a7)
	addi sp, sp, 256
	j 21f
20:
	addi a0, zero, 1
21:
	ret
	.option pop

vg_rc4_apply:
	.option push
	.option arch, +m, +c
	lbu a3, 256(a0)
	lbu t4, 257(a0)
	addi t6, zero, 0
	beqz a2, 20f
	addi sp, sp, -256
	addi a7, sp, 0
	lbu t0, 0(a0)
	sb t0, 0(a7)
	lbu t0, 1(a0)
	sb t0, 1(a7)
	lbu t0, 2(a0)
	sb t0, 2(a7)
	lbu t0, 3(a0)
	sb t0, 3(a7)
	lbu t0, 4(a0)
	sb t0, 4(a7)
	lbu t0, 5(a0)
	sb t0, 5(a7)
	lbu t0, 6(a0)
	sb t0, 6(a7)
	lbu t0, 7(a0)
	sb t0, 7(a7)
	lbu t0, 8(a0)
	sb t0, 8(a7)
	lbu t0, 9(a0)
	sb t0, 9(a7)
	lbu t0, 10(a0)
	sb t0, 10(a7)
	lbu t0, 11(a0)
	sb t0, 11(a7)
	lbu t0, 12(a0)
	sb t0, 12(a7)
	lbu t0, 13(a0)
	sb t0, 13(a7)
	lbu t0, 14(a0)
	sb t0, 14(a7)
	lbu t0, 15(a0)
	sb t0, 15(a7)
	lbu t0, 16(a0)
	sb t0, 16(a7)
	lbu t0, 17(a0)
	sb t0, 17(a7)
	lbu t0, 18(a0)
	sb t0, 18(a7)
	lbu t0, 19(a0)
	sb t0, 19(a7)
	lbu t0, 20(a0)
	sb t0, 20(a7)
	lbu t0, 21(a0)
	sb t0, 21(a7)
	lbu t0, 22(a0)
	sb t0, 22(a7)
	lbu t0, 23(a0)
	sb t0, 23(a7)
	lbu t0, 24(a0)
	sb t0, 24(a7)
	lbu t0, 25(a0)
	sb t0, 25(a7)
	lbu t0, 26(a0)
	sb t0, 26(a7)
	lbu t0, 27(a0)
	sb t0, 27(a7)
	lbu t0, 28(a0)
	sb t0, 28(a7)
	lbu t0, 29(a0)
	sb t0, 29(a7)
	lbu t0, 30(a0)
	sb t0, 30(a7)
	lbu t0, 31(a0)
	sb t0, 31(a7)
	lbu t0, 32(a0)
	sb t0, 32(a7)
	lbu t0, 33(a0)
	sb t0, 33(a7)
	lbu t0, 34(a0)
	sb t0, 34(a7)
	lbu t0, 35(a0)
	sb t0, 35(a7)
	lbu t0, 36(a0)
	sb t0, 36(a7)
	lbu t0, 37(a0)
	sb t0, 37(a7)
	lbu t0, 38(a0)
	sb t0, 38(a7)
	lbu t0, 39(a0)
	sb t0, 39(a7)
	lbu t0, 40(a0)
	sb t0, 40(a7)
	lbu t0, 41(a0)
	sb t0, 41(a7)
	lbu t0, 42(a0)
	sb t0, 42(a7)
	lbu t0, 43(a0)
	sb t0, 43(a7)
	lbu t0, 44(a0)
	sb t0, 44(a7)
	lbu t0, 45(a0)
	sb t0, 45(a7)
	lbu t0, 46(a0)
	sb t0, 46(a7)
	lbu t0, 47(a0)
	sb t0, 47(a7)
	lbu t0, 48(a0)
	sb t0, 48(a7)
	lbu t0, 49(a0)
	sb t0, 49(a7)
	lbu t0, 50(a0)
	sb t0, 50(a7)
	lbu t0, 51(a0)
	sb t0, 51(a7)
	lbu t0, 52(a0)
	sb t0, 52(a7)
	lbu t0, 53(a0)
	sb t0, 53(a7)
	lbu t0, 54(a0)
	sb t0, 54(a7)
	lbu t0, 55(a0)
	sb t0, 55(a7)
	lbu t0, 56(a0)
	sb t0, 56(a7)
	lbu t0, 57(a0)
	sb t0, 57(a7)
	lbu t0, 58(a0)
	sb t0, 58(a7)
	lbu t0, 59(a0)
	sb t0, 59(a7)
	lbu t0, 60(a0)
	sb t0, 60(a7)
	lbu t0, 61(a0)
	sb t0, 61(a7)
	lbu t0, 62(a0)
	sb t0, 62(a7)
	lbu t0, 63(a0)
	sb t0, 63(a7)
	lbu t0, 64(a0)
	sb t0, 64(a7)
	lbu t0, 65(a0)
	sb t0, 65(a7)
	lbu t0, 66(a0)
	sb t0, 66(a7)
	lbu t0, 67(a0)
	sb t0, 67(a7)
	lbu t0, 68(a0)
	sb t0, 68(a7)
	lbu t0, 69(a0)
	sb t0, 69(a7)
	lbu t0, 70(a0)
	sb t0, 70(a7)
	lbu t0, 71(a0)
	sb t0, 71(a7)
	lbu t0, 72(a0)
	sb t0, 72(a7)
	lbu t0, 73(a0)
	sb t0, 73(a7)
	lbu t0, 74(a0)
	sb t0, 74(a7)
	lbu t0, 75(a0)
	sb t0, 75(a7)
	lbu t0, 76(a0)
	sb t0, 76(a7)
	lbu t0, 77(a0)
	sb t0, 77(a7)
	lbu t0, 78(a0)
	sb t0, 78(a7)
	lbu t0, 79(a0)
	sb t0, 79(a7)
	lbu t0, 80(a0)
	sb t0, 80(a7)
	lbu t0, 81(a0)
	sb t0, 81(a7)
	lbu t0, 82(a0)
	sb t0, 82(a7)
	lbu t0, 83(a0)
	sb t0, 83(a7)
	lbu t0, 84(a0)
	sb t0, 84(a7)
	lbu t0, 85(a0)
	sb t0, 85(a7)
	lbu t0, 86(a0)
	sb t0, 86(a7)
	lbu t0, 87(a0)
	sb t0, 87(a7)
	lbu t0, 88(a0)
	sb t0, 88(a7)
	lbu t0, 89(a0)
	sb t0, 89(a7)
	lbu t0, 90(a0)
	sb t0, 90(a7)
	lbu t0, 91(a0)
	sb t0, 91(a7)
	lbu t0, 92(a0)
	sb t0, 92(a7)
	lbu t0, 93(a0)
	sb t0, 93(a7)
	lbu t0, 94(a0)
	sb t0, 94(a7)
	lbu t0, 95(a0)
	sb t0, 95(a7)
	lbu t0, 96(a0)
	sb t0, 96(a7)
	lbu t0, 97(a0)
	sb t0, 97(a7)
	lbu t0, 98(a0)
	sb t0, 98(a7)
	lbu t0, 99(a0)
	sb t0, 99(a7)
	lbu t0, 100(a0)
	sb t0, 100(a7)
	lbu t0, 101(a0)
	sb t0, 101(a7)
	lbu t0, 102(a0)
	sb t0, 102(a7)
	lbu t0, 103(a0)
	sb t0, 103(a7)
	lbu t0, 104(a0)
	sb t0, 104(a7)
	lbu t0, 105(a0)
	sb t0, 105(a7)
	lbu t0, 106(a0)
	sb t0, 106(a7)
	lbu t0, 107(a0)
	sb t0, 107(a7)
	lbu t0, 108(a0)
	sb t0, 108(a7)
	lbu t0, 109(a0)
	sb t0, 109(a7)
	lbu t0, 110(a0)
	sb t0, 110(a7)
	lbu t0, 111(a0)
	sb t0, 111(a7)
	lbu t0, 112(a0)
	sb t0, 112(a7)
	lbu t0, 113(a0)
	sb t0, 113(a7)
	lbu t0, 114(a0)
	sb t0, 114(a7)
	lbu t0, 115(a0)
	sb t0, 115(a7)
	lbu t0, 116(a0)
	sb t0, 116(a7)
	lbu t0, 117(a0)
	sb t0, 117(a7)
	lbu t0, 118(a0)
	sb t0, 118(a7)
	lbu t0, 119(a0)
	sb t0, 119(a7)
	lbu t0, 120(a0)
	sb t0, 120(a7)
	lbu t0, 121(a0)
	sb t0, 121(a7)
	lbu t0, 122(a0)
	sb t0, 122(a7)
	lbu t0, 123(a0)
	sb t0, 123(a7)
	lbu t0, 124(a0)
	sb t0, 124(a7)
	lbu t0, 125(a0)
	sb t0, 125(a7)
	lbu t0, 126(a0)
	sb t0, 126(a7)
	lbu t0, 127(a0)
	sb t0, 127(a7)
	lbu t0, 128(a0)
	sb t0, 128(a7)
	lbu t0, 129(a0)
	sb t0, 129(a7)
	lbu t0, 130(a0)
	sb t0, 130(a7)
	lbu t0, 131(a0)
	sb t0, 131(a7)
	lbu t0, 132(a0)
	sb t0, 132(a7)
	lbu t0, 133(a0)
	sb t0, 133(a7)
	lbu t0, 134(a0)
	sb t0, 134(a7)
	lbu t0, 135(a0)
	sb t0, 135(a7)
	lbu t0, 136(a0)
	sb t0, 136(a7)
	lbu t0, 137(a0)
	sb t0, 137(a7)
	lbu t0, 138(a0)
	sb t0, 138(a7)
	lbu t0, 139(a0)
	sb t0, 139(a7)
	lbu t0, 140(a0)
	sb t0, 140(a7)
	lbu t0, 141(a0)
	sb t0, 141(a7)
	lbu t0, 142(a0)
	sb t0, 142(a7)
	lbu t0, 143(a0)
	sb t0, 143(a7)
	lbu t0, 144(a0)
	sb t0, 144(a7)
	lbu t0, 145(a0)
	sb t0, 145(a7)
	lbu t0, 146(a0)
	sb t0, 146(a7)
	lbu t0, 147(a0)
	sb t0, 147(a7)
	lbu t0, 148(a0)
	sb t0, 148(a7)
	lbu t0, 149(a0)
	sb t0, 149(a7)
	lbu t0, 150(a0)
	sb t0, 150(a7)
	lbu t0, 151(a0)
	sb t0, 151(a7)
	lbu t0, 152(a0)
	sb t0, 152(a7)
	lbu t0, 153(a0)
	sb t0, 153(a7)
	lbu t0, 154(a0)
	sb t0, 154(a7)
	lbu t0, 155(a0)
	sb t0, 155(a7)
	lbu t0, 156(a0)
	sb t0, 156(a7)
	lbu t0, 157(a0)
	sb t0, 157(a7)
	lbu t0, 158(a0)
	sb t0, 158(a7)
	lbu t0, 159(a0)
	sb t0, 159(a7)
	lbu t0, 160(a0)
	sb t0, 160(a7)
	lbu t0, 161(a0)
	sb t0, 161(a7)
	lbu t0, 162(a0)
	sb t0, 162(a7)
	lbu t0, 163(a0)
	sb t0, 163(a7)
	lbu t0, 164(a0)
	sb t0, 164(a7)
	lbu t0, 165(a0)
	sb t0, 165(a7)
	lbu t0, 166(a0)
	sb t0, 166(a7)
	lbu t0, 167(a0)
	sb t0, 167(a7)
	lbu t0, 168(a0)
	sb t0, 168(a7)
	lbu t0, 169(a0)
	sb t0, 169(a7)
	lbu t0, 170(a0)
	sb t0, 170(a7)
	lbu t0, 171(a0)
	sb t0, 171(a7)
	lbu t0, 172(a0)
	sb t0, 172(a7)
	lbu t0, 173(a0)
	sb t0, 173(a7)
	lbu t0, 174(a0)
	sb t0, 174(a7)
	lbu t0, 175(a0)
	sb t0, 175(a7)
	lbu t0, 176(a0)
	sb t0, 176(a7)
	lbu t0, 177(a0)
	sb t0, 177(a7)
	lbu t0, 178(a0)
	sb t0, 178(a7)
	lbu t0, 179(a0)
	sb t0, 179(a7)
	lbu t0, 180(a0)
	sb t0, 180(a7)
	lbu t0, 181(a0)
	sb t0, 181(a7)
	lbu t0, 182(a0)
	sb t0, 182(a7)
	lbu t0, 183(a0)
	sb t0, 183(a7)
	lbu t0, 184(a0)
	sb t0, 184(a7)
	lbu t0, 185(a0)
	sb t0, 185(a7)
	lbu t0, 186(a0)
	sb t0, 186(a7)
	lbu t0, 187(a0)
	sb t0, 187(a7)
	lbu t0, 188(a0)
	sb t0, 188(a7)
	lbu t0, 189(a0)
	sb t0, 189(a7)
	lbu t0, 190(a0)
	sb t0, 190(a7)
	lbu t0, 191(a0)
	sb t0, 191(a7)
	lbu t0, 192(a0)
	sb t0, 192(a7)
	lbu t0, 193(a0)
	sb t0, 193(a7)
	lbu t0, 194(a0)
	sb t0, 194(a7)
	lbu t0, 195(a0)
	sb t0, 195(a7)
	lbu t0, 196(a0)
	sb t0, 196(a7)
	lbu t0, 197(a0)
	sb t0, 197(a7)
	lbu t0, 198(a0)
	sb t0, 198(a7)
	lbu t0, 199(a0)
	sb t0, 199(a7)
	lbu t0, 200(a0)
	sb t0, 200(a7)
	lbu t0, 201(a0)
	sb t0, 201(a7)
	lbu t0, 202(a0)
	sb t0, 202(a7)
	lbu t0, 203(a0)
	sb t0, 203(a7)
	lbu t0, 204(a0)
	sb t0, 204(a7)
	lbu t0, 205(a0)
	sb t0, 205(a7)
	lbu t0, 206(a0)
	sb t0, 206(a7)
	lbu t0, 207(a0)
	sb t0, 207(a7)
	lbu t0, 208(a0)
	sb t0, 208(a7)
	lbu t0, 209(a0)
	sb t0, 209(a7)
	lbu t0, 210(a0)
	sb t0, 210(a7)
	lbu t0, 211(a0)
	sb t0, 211(a7)
	lbu t0, 212(a0)
	sb t0, 212(a7)
	lbu t0, 213(a0)
	sb t0, 213(a7)
	lbu t0, 214(a0)
	sb t0, 214(a7)
	lbu t0, 215(a0)
	sb t0, 215(a7)
	lbu t0, 216(a0)
	sb t0, 216(a7)
	lbu t0, 217(a0)
	sb t0, 217(a7)
	lbu t0, 218(a0)
	sb t0, 218(a7)
	lbu t0, 219(a0)
	sb t0, 219(a7)
	lbu t0, 220(a0)
	sb t0, 220(a7)
	lbu t0, 221(a0)
	sb t0, 221(a7)
	lbu t0, 222(a0)
	sb t0, 222(a7)
	lbu t0, 223(a0)
	sb t0, 223(a7)
	lbu t0, 224(a0)
	sb t0, 224(a7)
	lbu t0, 225(a0)
	sb t0, 225(a7)
	lbu t0, 226(a0)
	sb t0, 226(a7)
	lbu t0, 227(a0)
	sb t0, 227(a7)
	lbu t0, 228(a0)
	sb t0, 228(a7)
	lbu t0, 229(a0)
	sb t0, 229(a7)
	lbu t0, 230(a0)
	sb t0, 230(a7)
	lbu t0, 231(a0)
	sb t0, 231(a7)
	lbu t0, 232(a0)
	sb t0, 232(a7)
	lbu t0, 233(a0)
	sb t0, 233(a7)
	lbu t0, 234(a0)
	sb t0, 234(a7)
	lbu t0, 235(a0)
	sb t0, 235(a7)
	lbu t0, 236(a0)
	sb t0, 236(a7)
	lbu t0, 237(a0)
	sb t0, 237(a7)
	lbu t0, 238(a0)
	sb t0, 238(a7)
	lbu t0, 239(a0)
	sb t0, 239(a7)
	lbu t0, 240(a0)
	sb t0, 240(a7)
	lbu t0, 241(a0)
	sb t0, 241(a7)
	lbu t0, 242(a0)
	sb t0, 242(a7)
	lbu t0, 243(a0)
	sb t0, 243(a7)
	lbu t0, 244(a0)
	sb t0, 244(a7)
	lbu t0, 245(a0)
	sb t0, 245(a7)
	lbu t0, 246(a0)
	sb t0, 246(a7)
	lbu t0, 247(a0)
	sb t0, 247(a7)
	lbu t0, 248(a0)
	sb t0, 248(a7)
	lbu t0, 249(a0)
	sb t0, 249(a7)
	lbu t0, 250(a0)
	sb t0, 250(a7)
	lbu t0, 251(a0)
	sb t0, 251(a7)
	lbu t0, 252(a0)
	sb t0, 252(a7)
	lbu t0, 253(a0)
	sb t0, 253(a7)
	lbu t0, 254(a0)
	sb t0, 254(a7)
	lbu t0, 255(a0)
	sb t0, 255(a7)
22:
	addi a3, a3, 1
	slli a3, a3, 56
	srli a3, a3, 56
	add t2, a7, a3
	lbu t0, 0(t2)
	add t4, t4, t0
	slli t4, t4, 56
	srli t4, t4, 56
	or a4, t4, t4
	srli t5, a4, 3
	addi t2, zero, 1
	sll t5, t2, t5
	slli t2, t5, 63
	srai t2, t2, 63
	ld t1, 0(a7)
	and t1, t1, t2
	slli t2, t5, 62
	srai t2, t2, 63
	ld t0, 8(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 61
	srai t2, t2, 63
	ld t0, 16(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 60
	srai t2, t2, 63
	ld t0, 24(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 59
	srai t2, t2, 63
	ld t0, 32(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 58
	srai t2, t2, 63
	ld t0, 40(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 57
	srai t2, t2, 63
	ld t0, 48(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 56
	srai t2, t2, 63
	ld t0, 56(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 55
	srai t2, t2, 63
	ld t0, 64(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 54
	srai t2, t2, 63
	ld t0, 72(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 53
	srai t2, t2, 63
	ld t0, 80(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 52
	srai t2, t2, 63
	ld t0, 88(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 51
	srai t2, t2, 63
	ld t0, 96(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 50
	srai t2, t2, 63
	ld t0, 104(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 49
	srai t2, t2, 63
	ld t0, 112(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 48
	srai t2, t2, 63
	ld t0, 120(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 47
	srai t2, t2, 63
	ld t0, 128(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 46
	srai t2, t2, 63
	ld t0, 136(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 45
	srai t2, t2, 63
	ld t0, 144(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 44
	srai t2, t2, 63
	ld t0, 152(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 43
	srai t2, t2, 63
	ld t0, 160(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 42
	srai t2, t2, 63
	ld t0, 168(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 41
	srai t2, t2, 63
	ld t0, 176(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 40
	srai t2, t2, 63
	ld t0, 184(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 39
	srai t2, t2, 63
	ld t0, 192(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 38
	srai t2, t2, 63
	ld t0, 200(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 37
	srai t2, t2, 63
	ld t0, 208(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 36
	srai t2, t2, 63
	ld t0, 216(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 35
	srai t2, t2, 63
	ld t0, 224(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 34
	srai t2, t2, 63
	ld t0, 232(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 33
	srai t2, t2, 63
	ld t0, 240(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 32
	srai t2, t2, 63
	ld t0, 248(a7)
	and t0, t0, t2
	or t1, t1, t0
	andi t2, a4, 7
	slli t2, t2, 3
	srl a5, t1, t2
	andi a5, a5, 255
	add t2, a7, a3
	lbu t0, 0(t2)
	xor a5, a5, t0
	andi t2, a4, 7
	slli t2, t2, 3
	sll t1, a5, t2
	add t2, a7, a3
	lbu t0, 0(t2)
	xor a5, a5, t0
	slli t2, t5, 63
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 0(a7)
	xor t0, t0, t2
	sd t0, 0(a7)
	slli t2, t5, 62
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 8(a7)
	xor t0, t0, t2
	sd t0, 8(a7)
	slli t2, t5, 61
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 16(a7)
	xor t0, t0, t2
	sd t0, 16(a7)
	slli t2, t5, 60
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 24(a7)
	xor t0, t0, t2
	sd t0, 24(a7)
	slli t2, t5, 59
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 32(a7)
	xor t0, t0, t2
	sd t0, 32(a7)
	slli t2, t5, 58
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 40(a7)
	xor t0, t0, t2
	sd t0, 40(a7)
	slli t2, t5, 57
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 48(a7)
	xor t0, t0, t2
	sd t0, 48(a7)
	slli t2, t5, 56
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 56(a7)
	xor t0, t0, t2
	sd t0, 56(a7)
	slli t2, t5, 55
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 64(a7)
	xor t0, t0, t2
	sd t0, 64(a7)
	slli t2, t5, 54
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 72(a7)
	xor t0, t0, t2
	sd t0, 72(a7)
	slli t2, t5, 53
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 80(a7)
	xor t0, t0, t2
	sd t0, 80(a7)
	slli t2, t5, 52
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 88(a7)
	xor t0, t0, t2
	sd t0, 88(a7)
	slli t2, t5, 51
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 96(a7)
	xor t0, t0, t2
	sd t0, 96(a7)
	slli t2, t5, 50
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 104(a7)
	xor t0, t0, t2
	sd t0, 104(a7)
	slli t2, t5, 49
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 112(a7)
	xor t0, t0, t2
	sd t0, 112(a7)
	slli t2, t5, 48
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 120(a7)
	xor t0, t0, t2
	sd t0, 120(a7)
	slli t2, t5, 47
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 128(a7)
	xor t0, t0, t2
	sd t0, 128(a7)
	slli t2, t5, 46
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 136(a7)
	xor t0, t0, t2
	sd t0, 136(a7)
	slli t2, t5, 45
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 144(a7)
	xor t0, t0, t2
	sd t0, 144(a7)
	slli t2, t5, 44
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 152(a7)
	xor t0, t0, t2
	sd t0, 152(a7)
	slli t2, t5, 43
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 160(a7)
	xor t0, t0, t2
	sd t0, 160(a7)
	slli t2, t5, 42
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 168(a7)
	xor t0, t0, t2
	sd t0, 168(a7)
	slli t2, t5, 41
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 176(a7)
	xor t0, t0, t2
	sd t0, 176(a7)
	slli t2, t5, 40
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 184(a7)
	xor t0, t0, t2
	sd t0, 184(a7)
	slli t2, t5, 39
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 192(a7)
	xor t0, t0, t2
	sd t0, 192(a7)
	slli t2, t5, 38
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 200(a7)
	xor t0, t0, t2
	sd t0, 200(a7)
	slli t2, t5, 37
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 208(a7)
	xor t0, t0, t2
	sd t0, 208(a7)
	slli t2, t5, 36
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 216(a7)
	xor t0, t0, t2
	sd t0, 216(a7)
	slli t2, t5, 35
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 224(a7)
	xor t0, t0, t2
	sd t0, 224(a7)
	slli t2, t5, 34
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 232(a7)
	xor t0, t0, t2
	sd t0, 232(a7)
	slli t2, t5, 33
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 240(a7)
	xor t0, t0, t2
	sd t0, 240(a7)
	slli t2, t5, 32
	srai t2, t2, 63
	and t2, t2, t1
	ld t0, 248(a7)
	xor t0, t0, t2
	sd t0, 248(a7)
	add t2, a7, a3
	lbu t0, 0(t2)
	sb a5, 0(t2)
	add a4, a5, t0
	slli a4, a4, 56
	srli a4, a4, 56
	srli t5, a4, 3
	addi t2, zero, 1
	sll t5, t2, t5
	slli t2, t5, 63
	srai t2, t2, 63
	ld t1, 0(a7)
	and t1, t1, t2
	slli t2, t5, 62
	srai t2, t2, 63
	ld t0, 8(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 61
	srai t2, t2, 63
	ld t0, 16(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 60
	srai t2, t2, 63
	ld t0, 24(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 59
	srai t2, t2, 63
	ld t0, 32(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 58
	srai t2, t2, 63
	ld t0, 40(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 57
	srai t2, t2, 63
	ld t0, 48(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 56
	srai t2, t2, 63
	ld t0, 56(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 55
	srai t2, t2, 63
	ld t0, 64(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 54
	srai t2, t2, 63
	ld t0, 72(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 53
	srai t2, t2, 63
	ld t0, 80(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 52
	srai t2, t2, 63
	ld t0, 88(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 51
	srai t2, t2, 63
	ld t0, 96(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 50
	srai t2, t2, 63
	ld t0, 104(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 49
	srai t2, t2, 63
	ld t0, 112(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 48
	srai t2, t2, 63
	ld t0, 120(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 47
	srai t2, t2, 63
	ld t0, 128(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 46
	srai t2, t2, 63
	ld t0, 136(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 45
	srai t2, t2, 63
	ld t0, 144(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 44
	srai t2, t2, 63
	ld t0, 152(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 43
	srai t2, t2, 63
	ld t0, 160(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 42
	srai t2, t2, 63
	ld t0, 168(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 41
	srai t2, t2, 63
	ld t0, 176(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 40
	srai t2, t2, 63
	ld t0, 184(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 39
	srai t2, t2, 63
	ld t0, 192(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 38
	srai t2, t2, 63
	ld t0, 200(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 37
	srai t2, t2, 63
	ld t0, 208(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 36
	srai t2, t2, 63
	ld t0, 216(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 35
	srai t2, t2, 63
	ld t0, 224(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 34
	srai t2, t2, 63
	ld t0, 232(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 33
	srai t2, t2, 63
	ld t0, 240(a7)
	and t0, t0, t2
	or t1, t1, t0
	slli t2, t5, 32
	srai t2, t2, 63
	ld t0, 248(a7)
	and t0, t0, t2
	or t1, t1, t0
	andi t2, a4, 7
	slli t2, t2, 3
	srl a5, t1, t2
	andi a5, a5, 255
	lbu t0, 0(a1)
	xor t0, t0, a5
	sb t0, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 22b
	lbu t0, 0(a7)
	sb t0, 0(a0)
	lbu t0, 1(a7)
	sb t0, 1(a0)
	lbu t0, 2(a7)
	sb t0, 2(a0)
	lbu t0, 3(a7)
	sb t0, 3(a0)
	lbu t0, 4(a7)
	sb t0, 4(a0)
	lbu t0, 5(a7)
	sb t0, 5(a0)
	lbu t0, 6(a7)
	sb t0, 6(a0)
	lbu t0, 7(a7)
	sb t0, 7(a0)
	lbu t0, 8(a7)
	sb t0, 8(a0)
	lbu t0, 9(a7)
	sb t0, 9(a0)
	lbu t0, 10(a7)
	sb t0, 10(a0)
	lbu t0, 11(a7)
	sb t0, 11(a0)
	lbu t0, 12(a7)
	sb t0, 12(a0)
	lbu t0, 13(a7)
	sb t0, 13(a0)
	lbu t0, 14(a7)
	sb t0, 14(a0)
	lbu t0, 15(a7)
	sb t0, 15(a0)
	lbu t0, 16(a7)
	sb t0, 16(a0)
	lbu t0, 17(a7)
	sb t0, 17(a0)
	lbu t0, 18(a7)
	sb t0, 18(a0)
	lbu t0, 19(a7)
	sb t0, 19(a0)
	lbu t0, 20(a7)
	sb t0, 20(a0)
	lbu t0, 21(a7)
	sb t0, 21(a0)
	lbu t0, 22(a7)
	sb t0, 22(a0)
	lbu t0, 23(a7)
	sb t0, 23(a0)
	lbu t0, 24(a7)
	sb t0, 24(a0)
	lbu t0, 25(a7)
	sb t0, 25(a0)
	lbu t0, 26(a7)
	sb t0, 26(a0)
	lbu t0, 27(a7)
	sb t0, 27(a0)
	lbu t0, 28(a7)
	sb t0, 28(a0)
	lbu t0, 29(a7)
	sb t0, 29(a0)
	lbu t0, 30(a7)
	sb t0, 30(a0)
	lbu t0, 31(a7)
	sb t0, 31(a0)
	lbu t0, 32(a7)
	sb t0, 32(a0)
	lbu t0, 33(a7)
	sb t0, 33(a0)
	lbu t0, 34(a7)
	sb t0, 34(a0)
	lbu t0, 35(a7)
	sb t0, 35(a0)
	lbu t0, 36(a7)
	sb t0, 36(a0)
	lbu t0, 37(a7)
	sb t0, 37(a0)
	lbu t0, 38(a7)
	sb t0, 38(a0)
	lbu t0, 39(a7)
	sb t0, 39(a0)
	lbu t0, 40(a7)
	sb t0, 40(a0)
	lbu t0, 41(a7)
	sb t0, 41(a0)
	lbu t0, 42(a7)
	sb t0, 42(a0)
	lbu t0, 43(a7)
	sb t0, 43(a0)
	lbu t0, 44(a7)
	sb t0, 44(a0)
	lbu t0, 45(a7)
	sb t0, 45(a0)
	lbu t0, 46(a7)
	sb t0, 46(a0)
	lbu t0, 47(a7)
	sb t0, 47(a0)
	lbu t0, 48(a7)
	sb t0, 48(a0)
	lbu t0, 49(a7)
	sb t0, 49(a0)
	lbu t0, 50(a7)
	sb t0, 50(a0)
	lbu t0, 51(a7)
	sb t0, 51(a0)
	lbu t0, 52(a7)
	sb t0, 52(a0)
	lbu t0, 53(a7)
	sb t0, 53(a0)
	lbu t0, 54(a7)
	sb t0, 54(a0)
	lbu t0, 55(a7)
	sb t0, 55(a0)
	lbu t0, 56(a7)
	sb t0, 56(a0)
	lbu t0, 57(a7)
	sb t0, 57(a0)
	lbu t0, 58(a7)
	sb t0, 58(a0)
	lbu t0, 59(a7)
	sb t0, 59(a0)
	lbu t0, 60(a7)
	sb t0, 60(a0)
	lbu t0, 61(a7)
	sb t0, 61(a0)
	lbu t0, 62(a7)
	sb t0, 62(a0)
	lbu t0, 63(a7)
	sb t0, 63(a0)
	lbu t0, 64(a7)
	sb t0, 64(a0)
	lbu t0, 65(a7)
	sb t0, 65(a0)
	lbu t0, 66(a7)
	sb t0, 66(a0)
	lbu t0, 67(a7)
	sb t0, 67(a0)
	lbu t0, 68(a7)
	sb t0, 68(a0)
	lbu t0, 69(a7)
	sb t0, 69(a0)
	lbu t0, 70(a7)
	sb t0, 70(a0)
	lbu t0, 71(a7)
	sb t0, 71(a0)
	lbu t0, 72(a7)
	sb t0, 72(a0)
	lbu t0, 73(a7)
	sb t0, 73(a0)
	lbu t0, 74(a7)
	sb t0, 74(a0)
	lbu t0, 75(a7)
	sb t0, 75(a0)
	lbu t0, 76(a7)
	sb t0, 76(a0)
	lbu t0, 77(a7)
	sb t0, 77(a0)
	lbu t0, 78(a7)
	sb t0, 78(a0)
	lbu t0, 79(a7)
	sb t0, 79(a0)
	lbu t0, 80(a7)
	sb t0, 80(a0)
	lbu t0, 81(a7)
	sb t0, 81(a0)
	lbu t0, 82(a7)
	sb t0, 82(a0)
	lbu t0, 83(a7)
	sb t0, 83(a0)
	lbu t0, 84(a7)
	sb t0, 84(a0)
	lbu t0, 85(a7)
	sb t0, 85(a0)
	lbu t0, 86(a7)
	sb t0, 86(a0)
	lbu t0, 87(a7)
	sb t0, 87(a0)
	lbu t0, 88(a7)
	sb t0, 88(a0)
	lbu t0, 89(a7)
	sb t0, 89(a0)
	lbu t0, 90(a7)
	sb t0, 90(a0)
	lbu t0, 91(a7)
	sb t0, 91(a0)
	lbu t0, 92(a7)
	sb t0, 92(a0)
	lbu t0, 93(a7)
	sb t0, 93(a0)
	lbu t0, 94(a7)
	sb t0, 94(a0)
	lbu t0, 95(a7)
	sb t0, 95(a0)
	lbu t0, 96(a7)
	sb t0, 96(a0)
	lbu t0, 97(a7)
	sb t0, 97(a0)
	lbu t0, 98(a7)
	sb t0, 98(a0)
	lbu t0, 99(a7)
	sb t0, 99(a0)
	lbu t0, 100(a7)
	sb t0, 100(a0)
	lbu t0, 101(a7)
	sb t0, 101(a0)
	lbu t0, 102(a7)
	sb t0, 102(a0)
	lbu t0, 103(a7)
	sb t0, 103(a0)
	lbu t0, 104(a7)
	sb t0, 104(a0)
	lbu t0, 105(a7)
	sb t0, 105(a0)
	lbu t0, 106(a7)
	sb t0, 106(a0)
	lbu t0, 107(a7)
	sb t0, 107(a0)
	lbu t0, 108(a7)
	sb t0, 108(a0)
	lbu t0, 109(a7)
	sb t0, 109(a0)
	lbu t0, 110(a7)
	sb t0, 110(a0)
	lbu t0, 111(a7)
	sb t0, 111(a0)
	lbu t0, 112(a7)
	sb t0, 112(a0)
	lbu t0, 113(a7)
	sb t0, 113(a0)
	lbu t0, 114(a7)
	sb t0, 114(a0)
	lbu t0, 115(a7)
	sb t0, 115(a0)
	lbu t0, 116(a7)
	sb t0, 116(a0)
	lbu t0, 117(a7)
	sb t0, 117(a0)
	lbu t0, 118(a7)
	sb t0, 118(a0)
	lbu t0, 119(a7)
	sb t0, 119(a0)
	lbu t0, 120(a7)
	sb t0, 120(a0)
	lbu t0, 121(a7)
	sb t0, 121(a0)
	lbu t0, 122(a7)
	sb t0, 122(a0)
	lbu t0, 123(a7)
	sb t0, 123(a0)
	lbu t0, 124(a7)
	sb t0, 124(a0)
	lbu t0, 125(a7)
	sb t0, 125(a0)
	lbu t0, 126(a7)
	sb t0, 126(a0)
	lbu t0, 127(a7)
	sb t0, 127(a0)
	lbu t0, 128(a7)
	sb t0, 128(a0)
	lbu t0, 129(a7)
	sb t0, 129(a0)
	lbu t0, 130(a7)
	sb t0, 130(a0)
	lbu t0, 131(a7)
	sb t0, 131(a0)
	lbu t0, 132(a7)
	sb t0, 132(a0)
	lbu t0, 133(a7)
	sb t0, 133(a0)
	lbu t0, 134(a7)
	sb t0, 134(a0)
	lbu t0, 135(a7)
	sb t0, 135(a0)
	lbu t0, 136(a7)
	sb t0, 136(a0)
	lbu t0, 137(a7)
	sb t0, 137(a0)
	lbu t0, 138(a7)
	sb t0, 138(a0)
	lbu t0, 139(a7)
	sb t0, 139(a0)
	lbu t0, 140(a7)
	sb t0, 140(a0)
	lbu t0, 141(a7)
	sb t0, 141(a0)
	lbu t0, 142(a7)
	sb t0, 142(a0)
	lbu t0, 143(a7)
	sb t0, 143(a0)
	lbu t0, 144(a7)
	sb t0, 144(a0)
	lbu t0, 145(a7)
	sb t0, 145(a0)
	lbu t0, 146(a7)
	sb t0, 146(a0)
	lbu t0, 147(a7)
	sb t0, 147(a0)
	lbu t0, 148(a7)
	sb t0, 148(a0)
	lbu t0, 149(a7)
	sb t0, 149(a0)
	lbu t0, 150(a7)
	sb t0, 150(a0)
	lbu t0, 151(a7)
	sb t0, 151(a0)
	lbu t0, 152(a7)
	sb t0, 152(a0)
	lbu t0, 153(a7)
	sb t0, 153(a0)
	lbu t0, 154(a7)
	sb t0, 154(a0)
	lbu t0, 155(a7)
	sb t0, 155(a0)
	lbu t0, 156(a7)
	sb t0, 156(a0)
	lbu t0, 157(a7)
	sb t0, 157(a0)
	lbu t0, 158(a7)
	sb t0, 158(a0)
	lbu t0, 159(a7)
	sb t0, 159(a0)
	lbu t0, 160(a7)
	sb t0, 160(a0)
	lbu t0, 161(a7)
	sb t0, 161(a0)
	lbu t0, 162(a7)
	sb t0, 162(a0)
	lbu t0, 163(a7)
	sb t0, 163(a0)
	lbu t0, 164(a7)
	sb t0, 164(a0)
	lbu t0, 165(a7)
	sb t0, 165(a0)
	lbu t0, 166(a7)
	sb t0, 166(a0)
	lbu t0, 167(a7)
	sb t0, 167(a0)
	lbu t0, 168(a7)
	sb t0, 168(a0)
	lbu t0, 169(a7)
	sb t0, 169(a0)
	lbu t0, 170(a7)
	sb t0, 170(a0)
	lbu t0, 171(a7)
	sb t0, 171(a0)
	lbu t0, 172(a7)
	sb t0, 172(a0)
	lbu t0, 173(a7)
	sb t0, 173(a0)
	lbu t0, 174(a7)
	sb t0, 174(a0)
	lbu t0, 175(a7)
	sb t0, 175(a0)
	lbu t0, 176(a7)
	sb t0, 176(a0)
	lbu t0, 177(a7)
	sb t0, 177(a0)
	lbu t0, 178(a7)
	sb t0, 178(a0)
	lbu t0, 179(a7)
	sb t0, 179(a0)
	lbu t0, 180(a7)
	sb t0, 180(a0)
	lbu t0, 181(a7)
	sb t0, 181(a0)
	lbu t0, 182(a7)
	sb t0, 182(a0)
	lbu t0, 183(a7)
	sb t0, 183(a0)
	lbu t0, 184(a7)
	sb t0, 184(a0)
	lbu t0, 185(a7)
	sb t0, 185(a0)
	lbu t0, 186(a7)
	sb t0, 186(a0)
	lbu t0, 187(a7)
	sb t0, 187(a0)
	lbu t0, 188(a7)
	sb t0, 188(a0)
	lbu t0, 189(a7)
	sb t0, 189(a0)
	lbu t0, 190(a7)
	sb t0, 190(a0)
	lbu t0, 191(a7)
	sb t0, 191(a0)
	lbu t0, 192(a7)
	sb t0, 192(a0)
	lbu t0, 193(a7)
	sb t0, 193(a0)
	lbu t0, 194(a7)
	sb t0, 194(a0)
	lbu t0, 195(a7)
	sb t0, 195(a0)
	lbu t0, 196(a7)
	sb t0, 196(a0)
	lbu t0, 197(a7)
	sb t0, 197(a0)
	lbu t0, 198(a7)
	sb t0, 198(a0)
	lbu t0, 199(a7)
	sb t0, 199(a0)
	lbu t0, 200(a7)
	sb t0, 200(a0)
	lbu t0, 201(a7)
	sb t0, 201(a0)
	lbu t0, 202(a7)
	sb t0, 202(a0)
	lbu t0, 203(a7)
	sb t0, 203(a0)
	lbu t0, 204(a7)
	sb t0, 204(a0)
	lbu t0, 205(a7)
	sb t0, 205(a0)
	lbu t0, 206(a7)
	sb t0, 206(a0)
	lbu t0, 207(a7)
	sb t0, 207(a0)
	lbu t0, 208(a7)
	sb t0, 208(a0)
	lbu t0, 209(a7)
	sb t0, 209(a0)
	lbu t0, 210(a7)
	sb t0, 210(a0)
	lbu t0, 211(a7)
	sb t0, 211(a0)
	lbu t0, 212(a7)
	sb t0, 212(a0)
	lbu t0, 213(a7)
	sb t0, 213(a0)
	lbu t0, 214(a7)
	sb t0, 214(a0)
	lbu t0, 215(a7)
	sb t0, 215(a0)
	lbu t0, 216(a7)
	sb t0, 216(a0)
	lbu t0, 217(a7)
	sb t0, 217(a0)
	lbu t0, 218(a7)
	sb t0, 218(a0)
	lbu t0, 219(a7)
	sb t0, 219(a0)
	lbu t0, 220(a7)
	sb t0, 220(a0)
	lbu t0, 221(a7)
	sb t0, 221(a0)
	lbu t0, 222(a7)
	sb t0, 222(a0)
	lbu t0, 223(a7)
	sb t0, 223(a0)
	lbu t0, 224(a7)
	sb t0, 224(a0)
	lbu t0, 225(a7)
	sb t0, 225(a0)
	lbu t0, 226(a7)
	sb t0, 226(a0)
	lbu t0, 227(a7)
	sb t0, 227(a0)
	lbu t0, 228(a7)
	sb t0, 228(a0)
	lbu t0, 229(a7)
	sb t0, 229(a0)
	lbu t0, 230(a7)
	sb t0, 230(a0)
	lbu t0, 231(a7)
	sb t0, 231(a0)
	lbu t0, 232(a7)
	sb t0, 232(a0)
	lbu t0, 233(a7)
	sb t0, 233(a0)
	lbu t0, 234(a7)
	sb t0, 234(a0)
	lbu t0, 235(a7)
	sb t0, 235(a0)
	lbu t0, 236(a7)
	sb t0, 236(a0)
	lbu t0, 237(a7)
	sb t0, 237(a0)
	lbu t0, 238(a7)
	sb t0, 238(a0)
	lbu t0, 239(a7)
	sb t0, 239(a0)
	lbu t0, 240(a7)
	sb t0, 240(a0)
	lbu t0, 241(a7)
	sb t0, 241(a0)
	lbu t0, 242(a7)
	sb t0, 242(a0)
	lbu t0, 243(a7)
	sb t0, 243(a0)
	lbu t0, 244(a7)
	sb t0, 244(a0)
	lbu t0, 245(a7)
	sb t0, 245(a0)
	lbu t0, 246(a7)
	sb t0, 246(a0)
	lbu t0, 247(a7)
	sb t0, 247(a0)
	lbu t0, 248(a7)
	sb t0, 248(a0)
	lbu t0, 249(a7)
	sb t0, 249(a0)
	lbu t0, 250(a7)
	sb t0, 250(a0)
	lbu t0, 251(a7)
	sb t0, 251(a0)
	lbu t0, 252(a7)
	sb t0, 252(a0)
	lbu t0, 253(a7)
	sb t0, 253(a0)
	lbu t0, 254(a7)
	sb t0, 254(a0)
	lbu t0, 255(a7)
	sb t0, 255(a0)
	sb a3, 256(a0)
	sb t4, 257(a0)
	sd t6, 0(a7)
	sd t6, 8(a7)
	sd t6, 16(a7)
	sd t6, 24(a7)
	sd t6, 32(a7)
	sd t6, 40(a7)
	sd t6, 48(a7)
	sd t6, 56(a7)
	sd t6, 64(a7)
	sd t6, 72(a7)
	sd t6, 80(a7)
	sd t6, 88(a7)
	sd t6, 96(a7)
	sd t6, 104(a7)
	sd t6, 112(a7)
	sd t6, 120(a7)
	sd t6, 128(a7)
	sd t6, 136(a7)
	sd t6, 144(a7)
	sd t6, 152(a7)
	sd t6, 160(a7)
	sd t6, 168(a7)
	sd t6, 176(a7)
	sd t6, 184(a7)
	sd t6, 192(a7)
	sd t6, 200(a7)
	sd t6, 208(a7)
	sd t6, 216(a7)
	sd t6, 224(a7)
	sd t6, 232(a7)
	sd t6, 240(a7)
	sd t6, 248(a7)
	addi sp, sp, 256
	j 21f
20:
21:
	ret
	.option pop
