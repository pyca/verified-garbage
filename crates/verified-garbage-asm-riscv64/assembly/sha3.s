// The functions of `src/sha3.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	.option push
	.option arch, +m, +c
	addi sp, sp, -608
	addi t6, sp, 0
	sd s0, 592(t6)
	sd s1, 600(t6)
	addi s1, a0, 0
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 130
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 138
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 139
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524288
	addiw t1, t1, 1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 129
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 9
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 138
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 64(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 136
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 72(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 9
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 80(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524288
	addiw t1, t1, 10
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 88(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 139
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 96(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 139
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 104(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 137
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 112(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 3
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 120(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 2
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 128(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 128
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 136(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 10
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 144(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524288
	addiw t1, t1, 10
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 152(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 129
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 160(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 8
	addiw t1, t1, 128
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 168(t6)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524288
	addiw t1, t1, 1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 176(t6)
	lui t0, 524288
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 524296
	addiw t1, t1, 8
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 184(t6)
	lbu t0, 0(s1)
	lbu t1, 1(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(s1)
	lbu t1, 5(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 192(t6)
	lbu t0, 8(s1)
	lbu t1, 9(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(s1)
	lbu t1, 13(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xori t0, t0, -1
	sd t0, 200(t6)
	lbu t0, 16(s1)
	lbu t1, 17(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 20(s1)
	lbu t1, 21(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 22(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 23(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xori t0, t0, -1
	sd t0, 208(t6)
	lbu t0, 24(s1)
	lbu t1, 25(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 28(s1)
	lbu t1, 29(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 216(t6)
	lbu t0, 32(s1)
	lbu t1, 33(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 36(s1)
	lbu t1, 37(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 38(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 39(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 224(t6)
	lbu t0, 40(s1)
	lbu t1, 41(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 44(s1)
	lbu t1, 45(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 46(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 47(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 232(t6)
	lbu t0, 48(s1)
	lbu t1, 49(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 52(s1)
	lbu t1, 53(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 54(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 55(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 240(t6)
	lbu t0, 56(s1)
	lbu t1, 57(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 60(s1)
	lbu t1, 61(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 62(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 63(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 248(t6)
	lbu t0, 64(s1)
	lbu t1, 65(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 66(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 67(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 68(s1)
	lbu t1, 69(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 70(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 71(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xori t0, t0, -1
	sd t0, 256(t6)
	lbu t0, 72(s1)
	lbu t1, 73(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 74(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 75(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 76(s1)
	lbu t1, 77(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 78(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 79(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 264(t6)
	lbu t0, 80(s1)
	lbu t1, 81(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 82(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 83(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 84(s1)
	lbu t1, 85(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 86(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 87(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 272(t6)
	lbu t0, 88(s1)
	lbu t1, 89(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 90(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 91(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 92(s1)
	lbu t1, 93(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 94(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 95(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 280(t6)
	lbu t0, 96(s1)
	lbu t1, 97(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 98(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 99(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 100(s1)
	lbu t1, 101(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 102(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 103(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xori t0, t0, -1
	sd t0, 288(t6)
	lbu t0, 104(s1)
	lbu t1, 105(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 106(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 107(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 108(s1)
	lbu t1, 109(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 110(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 111(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 296(t6)
	lbu t0, 112(s1)
	lbu t1, 113(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 114(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 115(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 116(s1)
	lbu t1, 117(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 118(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 119(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 304(t6)
	lbu t0, 120(s1)
	lbu t1, 121(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 122(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 123(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 124(s1)
	lbu t1, 125(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 126(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 127(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 312(t6)
	lbu t0, 128(s1)
	lbu t1, 129(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 130(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 131(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 132(s1)
	lbu t1, 133(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 134(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 135(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 320(t6)
	lbu t0, 136(s1)
	lbu t1, 137(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 138(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 139(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 140(s1)
	lbu t1, 141(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 142(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 143(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xori t0, t0, -1
	sd t0, 328(t6)
	lbu t0, 144(s1)
	lbu t1, 145(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 146(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 147(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 148(s1)
	lbu t1, 149(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 150(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 151(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 336(t6)
	lbu t0, 152(s1)
	lbu t1, 153(s1)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 154(s1)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 155(s1)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 156(s1)
	lbu t1, 157(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 158(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 159(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 344(t6)
	lbu a2, 160(s1)
	lbu t1, 161(s1)
	slli t1, t1, 8
	or a2, a2, t1
	lbu t1, 162(s1)
	slli t1, t1, 16
	or a2, a2, t1
	lbu t1, 163(s1)
	slli t1, t1, 24
	or a2, a2, t1
	lbu t2, 164(s1)
	lbu t1, 165(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 166(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 167(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or a2, a2, t2
	xori a2, a2, -1
	sd a2, 352(t6)
	lbu a3, 168(s1)
	lbu t1, 169(s1)
	slli t1, t1, 8
	or a3, a3, t1
	lbu t1, 170(s1)
	slli t1, t1, 16
	or a3, a3, t1
	lbu t1, 171(s1)
	slli t1, t1, 24
	or a3, a3, t1
	lbu t2, 172(s1)
	lbu t1, 173(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 174(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 175(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or a3, a3, t2
	sd a3, 360(t6)
	lbu a4, 176(s1)
	lbu t1, 177(s1)
	slli t1, t1, 8
	or a4, a4, t1
	lbu t1, 178(s1)
	slli t1, t1, 16
	or a4, a4, t1
	lbu t1, 179(s1)
	slli t1, t1, 24
	or a4, a4, t1
	lbu t2, 180(s1)
	lbu t1, 181(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 182(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 183(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or a4, a4, t2
	sd a4, 368(t6)
	lbu a5, 184(s1)
	lbu t1, 185(s1)
	slli t1, t1, 8
	or a5, a5, t1
	lbu t1, 186(s1)
	slli t1, t1, 16
	or a5, a5, t1
	lbu t1, 187(s1)
	slli t1, t1, 24
	or a5, a5, t1
	lbu t2, 188(s1)
	lbu t1, 189(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 190(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 191(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or a5, a5, t2
	sd a5, 376(t6)
	lbu a6, 192(s1)
	lbu t1, 193(s1)
	slli t1, t1, 8
	or a6, a6, t1
	lbu t1, 194(s1)
	slli t1, t1, 16
	or a6, a6, t1
	lbu t1, 195(s1)
	slli t1, t1, 24
	or a6, a6, t1
	lbu t2, 196(s1)
	lbu t1, 197(s1)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 198(s1)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 199(s1)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or a6, a6, t2
	sd a6, 384(t6)
	addi a0, sp, 192
	addi a1, sp, 392
	addi s0, t6, 0
20:
	ld a7, 0(a0)
	ld t0, 48(a0)
	ld t1, 96(a0)
	ld t2, 144(a0)
	ld t6, 16(a0)
	xor a4, a4, t6
	ld t6, 24(a0)
	xor a5, a5, t6
	xor a2, a2, a7
	ld t6, 8(a0)
	xor a3, a3, t6
	ld t6, 56(a0)
	xor a4, a4, t6
	ld t6, 40(a0)
	xor a2, a2, t6
	addi t3, a6, 0
	ld t6, 32(a0)
	xor a6, a6, t6
	xor a4, a4, t1
	ld t6, 80(a0)
	xor a2, a2, t6
	ld t6, 64(a0)
	xor a5, a5, t6
	xor a3, a3, t0
	ld t6, 72(a0)
	xor a6, a6, t6
	ld t6, 136(a0)
	xor a4, a4, t6
	ld t6, 120(a0)
	xor a2, a2, t6
	ld t6, 104(a0)
	xor a5, a5, t6
	ld t6, 88(a0)
	xor a3, a3, t6
	ld t6, 112(a0)
	xor a6, a6, t6
	addi t4, a4, 0
	slli t6, a4, 1
	srli a4, a4, 63
	or a4, a4, t6
	xor a4, a4, a2
	xor a5, a5, t2
	slli t6, a2, 1
	srli a2, a2, 63
	or a2, a2, t6
	xor a2, a2, a5
	ld t6, 128(a0)
	xor a3, a3, t6
	slli t6, a5, 1
	srli a5, a5, 63
	or a5, a5, t6
	xor a5, a5, a3
	ld t6, 152(a0)
	xor a6, a6, t6
	slli t6, a3, 1
	srli a3, a3, 63
	or a3, a3, t6
	xor a3, a3, a6
	slli t6, a6, 1
	srli a6, a6, 63
	or a6, a6, t6
	xor a6, a6, t4
	xor t0, t0, a4
	xor t1, t1, a5
	slli t6, t0, 44
	srli t0, t0, 20
	or t0, t0, t6
	xor t2, t2, a6
	xor t3, t3, a2
	slli t6, t1, 43
	srli t1, t1, 21
	or t1, t1, t6
	xor a7, a7, a3
	addi t4, t0, 0
	slli t6, t2, 21
	srli t2, t2, 43
	or t2, t2, t6
	or t0, t0, t1
	xor t0, t0, a7
	slli t6, t3, 14
	srli t3, t3, 50
	or t3, t3, t6
	ld t6, 0(s0)
	xor t0, t0, t6
	addi t5, t3, 0
	and t3, t3, t2
	sd t0, 0(a1)
	xor t3, t3, t1
	xori t1, t1, -1
	sd t3, 16(a1)
	or t1, t1, t2
	ld t3, 176(a0)
	xor t1, t1, t4
	sd t1, 8(a1)
	and t4, t4, a7
	ld t0, 72(a0)
	xor t4, t4, t5
	ld t1, 80(a0)
	sd t4, 32(a1)
	or t5, t5, a7
	ld a7, 24(a0)
	xor t5, t5, t2
	ld t2, 128(a0)
	sd t5, 24(a1)
	xor a7, a7, a6
	xor t3, t3, a5
	slli t6, a7, 28
	srli a7, a7, 36
	or a7, a7, t6
	xor t2, t2, a4
	xor t0, t0, a2
	slli t6, t3, 61
	srli t3, t3, 3
	or t3, t3, t6
	slli t6, t2, 45
	srli t2, t2, 19
	or t2, t2, t6
	xor t1, t1, a3
	slli t6, t0, 20
	srli t0, t0, 44
	or t0, t0, t6
	addi t4, a7, 0
	or a7, a7, t3
	slli t6, t1, 3
	srli t1, t1, 61
	or t1, t1, t6
	xor a7, a7, t2
	sd a7, 64(a1)
	addi t5, t0, 0
	and t0, t0, t4
	ld a7, 8(a0)
	xor t0, t0, t3
	xori t3, t3, -1
	sd t0, 72(a1)
	or t3, t3, t2
	ld t0, 56(a0)
	xor t3, t3, t1
	sd t3, 56(a1)
	and t2, t2, t1
	ld t3, 160(a0)
	xor t2, t2, t5
	sd t2, 48(a1)
	or t5, t5, t1
	ld t1, 104(a0)
	xor t5, t5, t4
	ld t2, 152(a0)
	sd t5, 40(a1)
	xor t1, t1, a6
	xor t2, t2, a2
	slli t6, t1, 25
	srli t1, t1, 39
	or t1, t1, t6
	xor t0, t0, a5
	slli t6, t2, 8
	srli t2, t2, 56
	or t2, t2, t6
	xor t3, t3, a3
	slli t6, t0, 6
	srli t0, t0, 58
	or t0, t0, t6
	xor a7, a7, a4
	slli t6, t3, 18
	srli t3, t3, 46
	or t3, t3, t6
	addi t4, t1, 0
	and t1, t1, t2
	slli t6, a7, 1
	srli a7, a7, 63
	or a7, a7, t6
	xori t2, t2, -1
	xor t1, t1, t0
	sd t1, 88(a1)
	addi t5, t3, 0
	and t3, t3, t2
	ld t1, 88(a0)
	xor t3, t3, t4
	sd t3, 96(a1)
	or t4, t4, t0
	ld t3, 184(a0)
	xor t4, t4, a7
	sd t4, 80(a1)
	and t0, t0, a7
	xor t0, t0, t5
	sd t0, 112(a1)
	or t5, t5, a7
	ld t0, 40(a0)
	xor t5, t5, t2
	ld t2, 136(a0)
	sd t5, 104(a1)
	ld a7, 32(a0)
	xor t1, t1, a4
	xor t2, t2, a5
	slli t6, t1, 10
	srli t1, t1, 54
	or t1, t1, t6
	xor t0, t0, a3
	slli t6, t2, 15
	srli t2, t2, 49
	or t2, t2, t6
	xor t3, t3, a6
	slli t6, t0, 36
	srli t0, t0, 28
	or t0, t0, t6
	xor a7, a7, a2
	slli t6, t3, 56
	srli t3, t3, 8
	or t3, t3, t6
	addi t4, t1, 0
	or t1, t1, t2
	slli t6, a7, 27
	srli a7, a7, 37
	or a7, a7, t6
	xori t2, t2, -1
	xor t1, t1, t0
	sd t1, 128(a1)
	addi t5, t3, 0
	or t3, t3, t2
	xor t3, t3, t4
	sd t3, 136(a1)
	and t4, t4, t0
	xor t4, t4, a7
	sd t4, 120(a1)
	or t0, t0, a7
	xor t0, t0, t5
	sd t0, 152(a1)
	and a7, a7, t5
	xor a7, a7, t2
	sd a7, 144(a1)
	ld t6, 16(a0)
	xor a5, a5, t6
	ld t6, 64(a0)
	xor a6, a6, t6
	slli t6, a5, 62
	srli a5, a5, 2
	or a5, a5, t6
	ld t6, 168(a0)
	xor a4, a4, t6
	slli t6, a6, 55
	srli a6, a6, 9
	or a6, a6, t6
	ld t6, 112(a0)
	xor a2, a2, t6
	slli t6, a4, 2
	srli a4, a4, 62
	or a4, a4, t6
	ld t6, 120(a0)
	xor a3, a3, t6
	slli t6, a2, 39
	srli a2, a2, 25
	or a2, a2, t6
	slli t6, a3, 41
	srli a3, a3, 23
	or a3, a3, t6
	addi t4, a5, 0
	and a5, a5, a6
	xori a6, a6, -1
	xor a5, a5, a4
	sd a5, 192(a1)
	addi t5, a2, 0
	and a2, a2, a6
	xor a2, a2, t4
	sd a2, 160(a1)
	or t4, t4, a4
	xor t4, t4, a3
	sd t4, 184(a1)
	and a4, a4, a3
	xor a4, a4, t5
	sd a4, 176(a1)
	or a3, a3, t5
	xor a3, a3, a6
	sd a3, 168(a1)
	addi a6, a5, 0
	addi a5, t4, 0
	ld a7, 0(a1)
	ld t0, 48(a1)
	ld t1, 96(a1)
	ld t2, 144(a1)
	ld t6, 16(a1)
	xor a4, a4, t6
	ld t6, 24(a1)
	xor a5, a5, t6
	xor a2, a2, a7
	ld t6, 8(a1)
	xor a3, a3, t6
	ld t6, 56(a1)
	xor a4, a4, t6
	ld t6, 40(a1)
	xor a2, a2, t6
	addi t3, a6, 0
	ld t6, 32(a1)
	xor a6, a6, t6
	xor a4, a4, t1
	ld t6, 80(a1)
	xor a2, a2, t6
	ld t6, 64(a1)
	xor a5, a5, t6
	xor a3, a3, t0
	ld t6, 72(a1)
	xor a6, a6, t6
	ld t6, 136(a1)
	xor a4, a4, t6
	ld t6, 120(a1)
	xor a2, a2, t6
	ld t6, 104(a1)
	xor a5, a5, t6
	ld t6, 88(a1)
	xor a3, a3, t6
	ld t6, 112(a1)
	xor a6, a6, t6
	addi t4, a4, 0
	slli t6, a4, 1
	srli a4, a4, 63
	or a4, a4, t6
	xor a4, a4, a2
	xor a5, a5, t2
	slli t6, a2, 1
	srli a2, a2, 63
	or a2, a2, t6
	xor a2, a2, a5
	ld t6, 128(a1)
	xor a3, a3, t6
	slli t6, a5, 1
	srli a5, a5, 63
	or a5, a5, t6
	xor a5, a5, a3
	ld t6, 152(a1)
	xor a6, a6, t6
	slli t6, a3, 1
	srli a3, a3, 63
	or a3, a3, t6
	xor a3, a3, a6
	slli t6, a6, 1
	srli a6, a6, 63
	or a6, a6, t6
	xor a6, a6, t4
	xor t0, t0, a4
	xor t1, t1, a5
	slli t6, t0, 44
	srli t0, t0, 20
	or t0, t0, t6
	xor t2, t2, a6
	xor t3, t3, a2
	slli t6, t1, 43
	srli t1, t1, 21
	or t1, t1, t6
	xor a7, a7, a3
	addi t4, t0, 0
	slli t6, t2, 21
	srli t2, t2, 43
	or t2, t2, t6
	or t0, t0, t1
	xor t0, t0, a7
	slli t6, t3, 14
	srli t3, t3, 50
	or t3, t3, t6
	ld t6, 8(s0)
	xor t0, t0, t6
	addi t5, t3, 0
	and t3, t3, t2
	sd t0, 0(a0)
	xor t3, t3, t1
	xori t1, t1, -1
	sd t3, 16(a0)
	or t1, t1, t2
	ld t3, 176(a1)
	xor t1, t1, t4
	sd t1, 8(a0)
	and t4, t4, a7
	ld t0, 72(a1)
	xor t4, t4, t5
	ld t1, 80(a1)
	sd t4, 32(a0)
	or t5, t5, a7
	ld a7, 24(a1)
	xor t5, t5, t2
	ld t2, 128(a1)
	sd t5, 24(a0)
	xor a7, a7, a6
	xor t3, t3, a5
	slli t6, a7, 28
	srli a7, a7, 36
	or a7, a7, t6
	xor t2, t2, a4
	xor t0, t0, a2
	slli t6, t3, 61
	srli t3, t3, 3
	or t3, t3, t6
	slli t6, t2, 45
	srli t2, t2, 19
	or t2, t2, t6
	xor t1, t1, a3
	slli t6, t0, 20
	srli t0, t0, 44
	or t0, t0, t6
	addi t4, a7, 0
	or a7, a7, t3
	slli t6, t1, 3
	srli t1, t1, 61
	or t1, t1, t6
	xor a7, a7, t2
	sd a7, 64(a0)
	addi t5, t0, 0
	and t0, t0, t4
	ld a7, 8(a1)
	xor t0, t0, t3
	xori t3, t3, -1
	sd t0, 72(a0)
	or t3, t3, t2
	ld t0, 56(a1)
	xor t3, t3, t1
	sd t3, 56(a0)
	and t2, t2, t1
	ld t3, 160(a1)
	xor t2, t2, t5
	sd t2, 48(a0)
	or t5, t5, t1
	ld t1, 104(a1)
	xor t5, t5, t4
	ld t2, 152(a1)
	sd t5, 40(a0)
	xor t1, t1, a6
	xor t2, t2, a2
	slli t6, t1, 25
	srli t1, t1, 39
	or t1, t1, t6
	xor t0, t0, a5
	slli t6, t2, 8
	srli t2, t2, 56
	or t2, t2, t6
	xor t3, t3, a3
	slli t6, t0, 6
	srli t0, t0, 58
	or t0, t0, t6
	xor a7, a7, a4
	slli t6, t3, 18
	srli t3, t3, 46
	or t3, t3, t6
	addi t4, t1, 0
	and t1, t1, t2
	slli t6, a7, 1
	srli a7, a7, 63
	or a7, a7, t6
	xori t2, t2, -1
	xor t1, t1, t0
	sd t1, 88(a0)
	addi t5, t3, 0
	and t3, t3, t2
	ld t1, 88(a1)
	xor t3, t3, t4
	sd t3, 96(a0)
	or t4, t4, t0
	ld t3, 184(a1)
	xor t4, t4, a7
	sd t4, 80(a0)
	and t0, t0, a7
	xor t0, t0, t5
	sd t0, 112(a0)
	or t5, t5, a7
	ld t0, 40(a1)
	xor t5, t5, t2
	ld t2, 136(a1)
	sd t5, 104(a0)
	ld a7, 32(a1)
	xor t1, t1, a4
	xor t2, t2, a5
	slli t6, t1, 10
	srli t1, t1, 54
	or t1, t1, t6
	xor t0, t0, a3
	slli t6, t2, 15
	srli t2, t2, 49
	or t2, t2, t6
	xor t3, t3, a6
	slli t6, t0, 36
	srli t0, t0, 28
	or t0, t0, t6
	xor a7, a7, a2
	slli t6, t3, 56
	srli t3, t3, 8
	or t3, t3, t6
	addi t4, t1, 0
	or t1, t1, t2
	slli t6, a7, 27
	srli a7, a7, 37
	or a7, a7, t6
	xori t2, t2, -1
	xor t1, t1, t0
	sd t1, 128(a0)
	addi t5, t3, 0
	or t3, t3, t2
	xor t3, t3, t4
	sd t3, 136(a0)
	and t4, t4, t0
	xor t4, t4, a7
	sd t4, 120(a0)
	or t0, t0, a7
	xor t0, t0, t5
	sd t0, 152(a0)
	and a7, a7, t5
	xor a7, a7, t2
	sd a7, 144(a0)
	ld t6, 16(a1)
	xor a5, a5, t6
	ld t6, 64(a1)
	xor a6, a6, t6
	slli t6, a5, 62
	srli a5, a5, 2
	or a5, a5, t6
	ld t6, 168(a1)
	xor a4, a4, t6
	slli t6, a6, 55
	srli a6, a6, 9
	or a6, a6, t6
	ld t6, 112(a1)
	xor a2, a2, t6
	slli t6, a4, 2
	srli a4, a4, 62
	or a4, a4, t6
	ld t6, 120(a1)
	xor a3, a3, t6
	slli t6, a2, 39
	srli a2, a2, 25
	or a2, a2, t6
	slli t6, a3, 41
	srli a3, a3, 23
	or a3, a3, t6
	addi t4, a5, 0
	and a5, a5, a6
	xori a6, a6, -1
	xor a5, a5, a4
	sd a5, 192(a0)
	addi t5, a2, 0
	and a2, a2, a6
	xor a2, a2, t4
	sd a2, 160(a0)
	or t4, t4, a4
	xor t4, t4, a3
	sd t4, 184(a0)
	and a4, a4, a3
	xor a4, a4, t5
	sd a4, 176(a0)
	or a3, a3, t5
	xor a3, a3, a6
	sd a3, 168(a0)
	addi a6, a5, 0
	addi a5, t4, 0
	addi s0, s0, 16
	bne s0, a0, 20b
	ld t0, 0(a0)
	sb t0, 0(s1)
	srli t1, t0, 8
	sb t1, 1(s1)
	srli t1, t0, 16
	sb t1, 2(s1)
	srli t1, t0, 24
	sb t1, 3(s1)
	srli t1, t0, 32
	sb t1, 4(s1)
	srli t2, t1, 8
	sb t2, 5(s1)
	srli t2, t1, 16
	sb t2, 6(s1)
	srli t2, t1, 24
	sb t2, 7(s1)
	ld t0, 8(a0)
	xori t0, t0, -1
	sb t0, 8(s1)
	srli t1, t0, 8
	sb t1, 9(s1)
	srli t1, t0, 16
	sb t1, 10(s1)
	srli t1, t0, 24
	sb t1, 11(s1)
	srli t1, t0, 32
	sb t1, 12(s1)
	srli t2, t1, 8
	sb t2, 13(s1)
	srli t2, t1, 16
	sb t2, 14(s1)
	srli t2, t1, 24
	sb t2, 15(s1)
	ld t0, 16(a0)
	xori t0, t0, -1
	sb t0, 16(s1)
	srli t1, t0, 8
	sb t1, 17(s1)
	srli t1, t0, 16
	sb t1, 18(s1)
	srli t1, t0, 24
	sb t1, 19(s1)
	srli t1, t0, 32
	sb t1, 20(s1)
	srli t2, t1, 8
	sb t2, 21(s1)
	srli t2, t1, 16
	sb t2, 22(s1)
	srli t2, t1, 24
	sb t2, 23(s1)
	ld t0, 24(a0)
	sb t0, 24(s1)
	srli t1, t0, 8
	sb t1, 25(s1)
	srli t1, t0, 16
	sb t1, 26(s1)
	srli t1, t0, 24
	sb t1, 27(s1)
	srli t1, t0, 32
	sb t1, 28(s1)
	srli t2, t1, 8
	sb t2, 29(s1)
	srli t2, t1, 16
	sb t2, 30(s1)
	srli t2, t1, 24
	sb t2, 31(s1)
	ld t0, 32(a0)
	sb t0, 32(s1)
	srli t1, t0, 8
	sb t1, 33(s1)
	srli t1, t0, 16
	sb t1, 34(s1)
	srli t1, t0, 24
	sb t1, 35(s1)
	srli t1, t0, 32
	sb t1, 36(s1)
	srli t2, t1, 8
	sb t2, 37(s1)
	srli t2, t1, 16
	sb t2, 38(s1)
	srli t2, t1, 24
	sb t2, 39(s1)
	ld t0, 40(a0)
	sb t0, 40(s1)
	srli t1, t0, 8
	sb t1, 41(s1)
	srli t1, t0, 16
	sb t1, 42(s1)
	srli t1, t0, 24
	sb t1, 43(s1)
	srli t1, t0, 32
	sb t1, 44(s1)
	srli t2, t1, 8
	sb t2, 45(s1)
	srli t2, t1, 16
	sb t2, 46(s1)
	srli t2, t1, 24
	sb t2, 47(s1)
	ld t0, 48(a0)
	sb t0, 48(s1)
	srli t1, t0, 8
	sb t1, 49(s1)
	srli t1, t0, 16
	sb t1, 50(s1)
	srli t1, t0, 24
	sb t1, 51(s1)
	srli t1, t0, 32
	sb t1, 52(s1)
	srli t2, t1, 8
	sb t2, 53(s1)
	srli t2, t1, 16
	sb t2, 54(s1)
	srli t2, t1, 24
	sb t2, 55(s1)
	ld t0, 56(a0)
	sb t0, 56(s1)
	srli t1, t0, 8
	sb t1, 57(s1)
	srli t1, t0, 16
	sb t1, 58(s1)
	srli t1, t0, 24
	sb t1, 59(s1)
	srli t1, t0, 32
	sb t1, 60(s1)
	srli t2, t1, 8
	sb t2, 61(s1)
	srli t2, t1, 16
	sb t2, 62(s1)
	srli t2, t1, 24
	sb t2, 63(s1)
	ld t0, 64(a0)
	xori t0, t0, -1
	sb t0, 64(s1)
	srli t1, t0, 8
	sb t1, 65(s1)
	srli t1, t0, 16
	sb t1, 66(s1)
	srli t1, t0, 24
	sb t1, 67(s1)
	srli t1, t0, 32
	sb t1, 68(s1)
	srli t2, t1, 8
	sb t2, 69(s1)
	srli t2, t1, 16
	sb t2, 70(s1)
	srli t2, t1, 24
	sb t2, 71(s1)
	ld t0, 72(a0)
	sb t0, 72(s1)
	srli t1, t0, 8
	sb t1, 73(s1)
	srli t1, t0, 16
	sb t1, 74(s1)
	srli t1, t0, 24
	sb t1, 75(s1)
	srli t1, t0, 32
	sb t1, 76(s1)
	srli t2, t1, 8
	sb t2, 77(s1)
	srli t2, t1, 16
	sb t2, 78(s1)
	srli t2, t1, 24
	sb t2, 79(s1)
	ld t0, 80(a0)
	sb t0, 80(s1)
	srli t1, t0, 8
	sb t1, 81(s1)
	srli t1, t0, 16
	sb t1, 82(s1)
	srli t1, t0, 24
	sb t1, 83(s1)
	srli t1, t0, 32
	sb t1, 84(s1)
	srli t2, t1, 8
	sb t2, 85(s1)
	srli t2, t1, 16
	sb t2, 86(s1)
	srli t2, t1, 24
	sb t2, 87(s1)
	ld t0, 88(a0)
	sb t0, 88(s1)
	srli t1, t0, 8
	sb t1, 89(s1)
	srli t1, t0, 16
	sb t1, 90(s1)
	srli t1, t0, 24
	sb t1, 91(s1)
	srli t1, t0, 32
	sb t1, 92(s1)
	srli t2, t1, 8
	sb t2, 93(s1)
	srli t2, t1, 16
	sb t2, 94(s1)
	srli t2, t1, 24
	sb t2, 95(s1)
	ld t0, 96(a0)
	xori t0, t0, -1
	sb t0, 96(s1)
	srli t1, t0, 8
	sb t1, 97(s1)
	srli t1, t0, 16
	sb t1, 98(s1)
	srli t1, t0, 24
	sb t1, 99(s1)
	srli t1, t0, 32
	sb t1, 100(s1)
	srli t2, t1, 8
	sb t2, 101(s1)
	srli t2, t1, 16
	sb t2, 102(s1)
	srli t2, t1, 24
	sb t2, 103(s1)
	ld t0, 104(a0)
	sb t0, 104(s1)
	srli t1, t0, 8
	sb t1, 105(s1)
	srli t1, t0, 16
	sb t1, 106(s1)
	srli t1, t0, 24
	sb t1, 107(s1)
	srli t1, t0, 32
	sb t1, 108(s1)
	srli t2, t1, 8
	sb t2, 109(s1)
	srli t2, t1, 16
	sb t2, 110(s1)
	srli t2, t1, 24
	sb t2, 111(s1)
	ld t0, 112(a0)
	sb t0, 112(s1)
	srli t1, t0, 8
	sb t1, 113(s1)
	srli t1, t0, 16
	sb t1, 114(s1)
	srli t1, t0, 24
	sb t1, 115(s1)
	srli t1, t0, 32
	sb t1, 116(s1)
	srli t2, t1, 8
	sb t2, 117(s1)
	srli t2, t1, 16
	sb t2, 118(s1)
	srli t2, t1, 24
	sb t2, 119(s1)
	ld t0, 120(a0)
	sb t0, 120(s1)
	srli t1, t0, 8
	sb t1, 121(s1)
	srli t1, t0, 16
	sb t1, 122(s1)
	srli t1, t0, 24
	sb t1, 123(s1)
	srli t1, t0, 32
	sb t1, 124(s1)
	srli t2, t1, 8
	sb t2, 125(s1)
	srli t2, t1, 16
	sb t2, 126(s1)
	srli t2, t1, 24
	sb t2, 127(s1)
	ld t0, 128(a0)
	sb t0, 128(s1)
	srli t1, t0, 8
	sb t1, 129(s1)
	srli t1, t0, 16
	sb t1, 130(s1)
	srli t1, t0, 24
	sb t1, 131(s1)
	srli t1, t0, 32
	sb t1, 132(s1)
	srli t2, t1, 8
	sb t2, 133(s1)
	srli t2, t1, 16
	sb t2, 134(s1)
	srli t2, t1, 24
	sb t2, 135(s1)
	ld t0, 136(a0)
	xori t0, t0, -1
	sb t0, 136(s1)
	srli t1, t0, 8
	sb t1, 137(s1)
	srli t1, t0, 16
	sb t1, 138(s1)
	srli t1, t0, 24
	sb t1, 139(s1)
	srli t1, t0, 32
	sb t1, 140(s1)
	srli t2, t1, 8
	sb t2, 141(s1)
	srli t2, t1, 16
	sb t2, 142(s1)
	srli t2, t1, 24
	sb t2, 143(s1)
	ld t0, 144(a0)
	sb t0, 144(s1)
	srli t1, t0, 8
	sb t1, 145(s1)
	srli t1, t0, 16
	sb t1, 146(s1)
	srli t1, t0, 24
	sb t1, 147(s1)
	srli t1, t0, 32
	sb t1, 148(s1)
	srli t2, t1, 8
	sb t2, 149(s1)
	srli t2, t1, 16
	sb t2, 150(s1)
	srli t2, t1, 24
	sb t2, 151(s1)
	ld t0, 152(a0)
	sb t0, 152(s1)
	srli t1, t0, 8
	sb t1, 153(s1)
	srli t1, t0, 16
	sb t1, 154(s1)
	srli t1, t0, 24
	sb t1, 155(s1)
	srli t1, t0, 32
	sb t1, 156(s1)
	srli t2, t1, 8
	sb t2, 157(s1)
	srli t2, t1, 16
	sb t2, 158(s1)
	srli t2, t1, 24
	sb t2, 159(s1)
	ld t0, 160(a0)
	xori t0, t0, -1
	sb t0, 160(s1)
	srli t1, t0, 8
	sb t1, 161(s1)
	srli t1, t0, 16
	sb t1, 162(s1)
	srli t1, t0, 24
	sb t1, 163(s1)
	srli t1, t0, 32
	sb t1, 164(s1)
	srli t2, t1, 8
	sb t2, 165(s1)
	srli t2, t1, 16
	sb t2, 166(s1)
	srli t2, t1, 24
	sb t2, 167(s1)
	ld t0, 168(a0)
	sb t0, 168(s1)
	srli t1, t0, 8
	sb t1, 169(s1)
	srli t1, t0, 16
	sb t1, 170(s1)
	srli t1, t0, 24
	sb t1, 171(s1)
	srli t1, t0, 32
	sb t1, 172(s1)
	srli t2, t1, 8
	sb t2, 173(s1)
	srli t2, t1, 16
	sb t2, 174(s1)
	srli t2, t1, 24
	sb t2, 175(s1)
	ld t0, 176(a0)
	sb t0, 176(s1)
	srli t1, t0, 8
	sb t1, 177(s1)
	srli t1, t0, 16
	sb t1, 178(s1)
	srli t1, t0, 24
	sb t1, 179(s1)
	srli t1, t0, 32
	sb t1, 180(s1)
	srli t2, t1, 8
	sb t2, 181(s1)
	srli t2, t1, 16
	sb t2, 182(s1)
	srli t2, t1, 24
	sb t2, 183(s1)
	ld t0, 184(a0)
	sb t0, 184(s1)
	srli t1, t0, 8
	sb t1, 185(s1)
	srli t1, t0, 16
	sb t1, 186(s1)
	srli t1, t0, 24
	sb t1, 187(s1)
	srli t1, t0, 32
	sb t1, 188(s1)
	srli t2, t1, 8
	sb t2, 189(s1)
	srli t2, t1, 16
	sb t2, 190(s1)
	srli t2, t1, 24
	sb t2, 191(s1)
	ld t0, 192(a0)
	sb t0, 192(s1)
	srli t1, t0, 8
	sb t1, 193(s1)
	srli t1, t0, 16
	sb t1, 194(s1)
	srli t1, t0, 24
	sb t1, 195(s1)
	srli t1, t0, 32
	sb t1, 196(s1)
	srli t2, t1, 8
	sb t2, 197(s1)
	srli t2, t1, 16
	sb t2, 198(s1)
	srli t2, t1, 24
	sb t2, 199(s1)
	ld s0, 400(a0)
	ld s1, 408(a0)
	addi sp, sp, 608
	ret
	.option pop

vg_keccak_absorb:
	.option push
	.option arch, +m, +c
	addi sp, sp, -560
	addi t0, sp, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	beqz s6, 20f
22:
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, sp, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	addi sp, sp, 560
	ret
	.option pop

vg_keccak_pad:
	.option push
	.option arch, +m, +c
	addi sp, sp, -528
	addi t0, sp, 0
	sd ra, 512(t0)
	add t1, a0, a2
	lbu t2, 0(t1)
	xor t2, t2, a3
	sb t2, 0(t1)
	add t1, a0, a1
	addi t1, t1, -1
	lbu t2, 0(t1)
	xori t2, t2, 128
	sb t2, 0(t1)
	addi a1, sp, 0
	call {vg_keccak_f1600}
	addi t0, sp, 0
	ld ra, 512(t0)
	addi sp, sp, 528
	ret
	.option pop

vg_keccak_squeeze:
	.option push
	.option arch, +m, +c
	addi sp, sp, -560
	addi t0, sp, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	beqz s6, 20f
22:
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
	add t2, s2, s4
	lbu t1, 0(t2)
	sb t1, 0(s5)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, sp, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	addi sp, sp, 560
	ret
	.option pop
