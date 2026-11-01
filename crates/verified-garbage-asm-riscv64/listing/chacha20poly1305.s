// The functions of `src/chacha20poly1305.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -624
	addi a7, sp, 0
	addi t0, a7, 7
	andi t0, t0, -8
	sd s7, 560(t0)
	sd s8, 568(t0)
	sd s9, 576(t0)
	sd s10, 584(t0)
	sd s11, 592(t0)
	sd ra, 600(t0)
	addi s7, a2, 0
	addi s8, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	addi t1, zero, 101
	sb t1, 0(t0)
	addi t1, zero, 120
	sb t1, 1(t0)
	addi t1, zero, 112
	sb t1, 2(t0)
	addi t1, zero, 97
	sb t1, 3(t0)
	addi t1, zero, 110
	sb t1, 4(t0)
	addi t1, zero, 100
	sb t1, 5(t0)
	addi t1, zero, 32
	sb t1, 6(t0)
	addi t1, zero, 51
	sb t1, 7(t0)
	addi t1, zero, 50
	sb t1, 8(t0)
	addi t1, zero, 45
	sb t1, 9(t0)
	addi t1, zero, 98
	sb t1, 10(t0)
	addi t1, zero, 121
	sb t1, 11(t0)
	addi t1, zero, 116
	sb t1, 12(t0)
	addi t1, zero, 101
	sb t1, 13(t0)
	addi t1, zero, 32
	sb t1, 14(t0)
	addi t1, zero, 107
	sb t1, 15(t0)
	lbu t1, 0(a0)
	sb t1, 16(t0)
	lbu t1, 1(a0)
	sb t1, 17(t0)
	lbu t1, 2(a0)
	sb t1, 18(t0)
	lbu t1, 3(a0)
	sb t1, 19(t0)
	lbu t1, 4(a0)
	sb t1, 20(t0)
	lbu t1, 5(a0)
	sb t1, 21(t0)
	lbu t1, 6(a0)
	sb t1, 22(t0)
	lbu t1, 7(a0)
	sb t1, 23(t0)
	lbu t1, 8(a0)
	sb t1, 24(t0)
	lbu t1, 9(a0)
	sb t1, 25(t0)
	lbu t1, 10(a0)
	sb t1, 26(t0)
	lbu t1, 11(a0)
	sb t1, 27(t0)
	lbu t1, 12(a0)
	sb t1, 28(t0)
	lbu t1, 13(a0)
	sb t1, 29(t0)
	lbu t1, 14(a0)
	sb t1, 30(t0)
	lbu t1, 15(a0)
	sb t1, 31(t0)
	lbu t1, 16(a0)
	sb t1, 32(t0)
	lbu t1, 17(a0)
	sb t1, 33(t0)
	lbu t1, 18(a0)
	sb t1, 34(t0)
	lbu t1, 19(a0)
	sb t1, 35(t0)
	lbu t1, 20(a0)
	sb t1, 36(t0)
	lbu t1, 21(a0)
	sb t1, 37(t0)
	lbu t1, 22(a0)
	sb t1, 38(t0)
	lbu t1, 23(a0)
	sb t1, 39(t0)
	lbu t1, 24(a0)
	sb t1, 40(t0)
	lbu t1, 25(a0)
	sb t1, 41(t0)
	lbu t1, 26(a0)
	sb t1, 42(t0)
	lbu t1, 27(a0)
	sb t1, 43(t0)
	lbu t1, 28(a0)
	sb t1, 44(t0)
	lbu t1, 29(a0)
	sb t1, 45(t0)
	lbu t1, 30(a0)
	sb t1, 46(t0)
	lbu t1, 31(a0)
	sb t1, 47(t0)
	addi t1, zero, 0
	sb t1, 48(t0)
	addi t1, zero, 0
	sb t1, 49(t0)
	addi t1, zero, 0
	sb t1, 50(t0)
	addi t1, zero, 0
	sb t1, 51(t0)
	lbu t1, 0(a1)
	sb t1, 52(t0)
	lbu t1, 1(a1)
	sb t1, 53(t0)
	lbu t1, 2(a1)
	sb t1, 54(t0)
	lbu t1, 3(a1)
	sb t1, 55(t0)
	lbu t1, 4(a1)
	sb t1, 56(t0)
	lbu t1, 5(a1)
	sb t1, 57(t0)
	lbu t1, 6(a1)
	sb t1, 58(t0)
	lbu t1, 7(a1)
	sb t1, 59(t0)
	lbu t1, 8(a1)
	sb t1, 60(t0)
	lbu t1, 9(a1)
	sb t1, 61(t0)
	lbu t1, 10(a1)
	sb t1, 62(t0)
	lbu t1, 11(a1)
	sb t1, 63(t0)
	addi t1, zero, 0
	sd t1, 512(t0)
	sd t1, 520(t0)
	sd s8, 528(t0)
	sd s10, 536(t0)
	addi a0, t0, 0
	addi a1, a0, 64
	call {vg_chacha20_block}
	addi a1, a0, 64
	addi a0, a0, 384
	call {vg_poly1305_init}
	addi a1, zero, 0
	addi a2, s7, 0
	addi a3, s8, 0
	call {vg_poly1305_update}
	addi a1, s8, 0
	addi a3, zero, 0
	sub a3, a3, s8
	andi a3, a3, 15
	addi a2, a0, 128
	call {vg_poly1305_update}
	addi a0, a0, -384
	addi t0, zero, 1
	sb t0, 48(a0)
	addi a1, s9, 0
	addi a2, s10, 0
	addi a3, a0, 64
	call {vg_chacha20_xor}
	addi a0, a0, 384
	addi a1, s8, 15
	andi a1, a1, -16
	addi a2, s9, 0
	addi a3, s10, 0
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	add a1, a1, s10
	addi a3, zero, 0
	sub a3, a3, s10
	andi a3, a3, 15
	addi a2, a0, 128
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	addi t0, s10, 15
	andi t0, t0, -16
	add a1, a1, t0
	addi a2, a0, 144
	addi a3, zero, 16
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	addi t0, s10, 15
	andi t0, t0, -16
	add a1, a1, t0
	addi a1, a1, 16
	addi a2, s11, 0
	call {vg_poly1305_finalize}
	addi t0, a0, -384
	ld s7, 560(t0)
	ld s8, 568(t0)
	ld s9, 576(t0)
	ld s10, 584(t0)
	ld s11, 592(t0)
	ld ra, 600(t0)
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
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	addi sp, sp, 624
	ret
	.option pop

vg_chacha20_poly1305_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -624
	addi a7, sp, 0
	addi t0, a7, 7
	andi t0, t0, -8
	sd s7, 560(t0)
	sd s8, 568(t0)
	sd s9, 576(t0)
	sd s10, 584(t0)
	sd s11, 592(t0)
	sd ra, 600(t0)
	addi s7, a2, 0
	addi s8, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	addi t1, zero, 101
	sb t1, 0(t0)
	addi t1, zero, 120
	sb t1, 1(t0)
	addi t1, zero, 112
	sb t1, 2(t0)
	addi t1, zero, 97
	sb t1, 3(t0)
	addi t1, zero, 110
	sb t1, 4(t0)
	addi t1, zero, 100
	sb t1, 5(t0)
	addi t1, zero, 32
	sb t1, 6(t0)
	addi t1, zero, 51
	sb t1, 7(t0)
	addi t1, zero, 50
	sb t1, 8(t0)
	addi t1, zero, 45
	sb t1, 9(t0)
	addi t1, zero, 98
	sb t1, 10(t0)
	addi t1, zero, 121
	sb t1, 11(t0)
	addi t1, zero, 116
	sb t1, 12(t0)
	addi t1, zero, 101
	sb t1, 13(t0)
	addi t1, zero, 32
	sb t1, 14(t0)
	addi t1, zero, 107
	sb t1, 15(t0)
	lbu t1, 0(a0)
	sb t1, 16(t0)
	lbu t1, 1(a0)
	sb t1, 17(t0)
	lbu t1, 2(a0)
	sb t1, 18(t0)
	lbu t1, 3(a0)
	sb t1, 19(t0)
	lbu t1, 4(a0)
	sb t1, 20(t0)
	lbu t1, 5(a0)
	sb t1, 21(t0)
	lbu t1, 6(a0)
	sb t1, 22(t0)
	lbu t1, 7(a0)
	sb t1, 23(t0)
	lbu t1, 8(a0)
	sb t1, 24(t0)
	lbu t1, 9(a0)
	sb t1, 25(t0)
	lbu t1, 10(a0)
	sb t1, 26(t0)
	lbu t1, 11(a0)
	sb t1, 27(t0)
	lbu t1, 12(a0)
	sb t1, 28(t0)
	lbu t1, 13(a0)
	sb t1, 29(t0)
	lbu t1, 14(a0)
	sb t1, 30(t0)
	lbu t1, 15(a0)
	sb t1, 31(t0)
	lbu t1, 16(a0)
	sb t1, 32(t0)
	lbu t1, 17(a0)
	sb t1, 33(t0)
	lbu t1, 18(a0)
	sb t1, 34(t0)
	lbu t1, 19(a0)
	sb t1, 35(t0)
	lbu t1, 20(a0)
	sb t1, 36(t0)
	lbu t1, 21(a0)
	sb t1, 37(t0)
	lbu t1, 22(a0)
	sb t1, 38(t0)
	lbu t1, 23(a0)
	sb t1, 39(t0)
	lbu t1, 24(a0)
	sb t1, 40(t0)
	lbu t1, 25(a0)
	sb t1, 41(t0)
	lbu t1, 26(a0)
	sb t1, 42(t0)
	lbu t1, 27(a0)
	sb t1, 43(t0)
	lbu t1, 28(a0)
	sb t1, 44(t0)
	lbu t1, 29(a0)
	sb t1, 45(t0)
	lbu t1, 30(a0)
	sb t1, 46(t0)
	lbu t1, 31(a0)
	sb t1, 47(t0)
	addi t1, zero, 0
	sb t1, 48(t0)
	addi t1, zero, 0
	sb t1, 49(t0)
	addi t1, zero, 0
	sb t1, 50(t0)
	addi t1, zero, 0
	sb t1, 51(t0)
	lbu t1, 0(a1)
	sb t1, 52(t0)
	lbu t1, 1(a1)
	sb t1, 53(t0)
	lbu t1, 2(a1)
	sb t1, 54(t0)
	lbu t1, 3(a1)
	sb t1, 55(t0)
	lbu t1, 4(a1)
	sb t1, 56(t0)
	lbu t1, 5(a1)
	sb t1, 57(t0)
	lbu t1, 6(a1)
	sb t1, 58(t0)
	lbu t1, 7(a1)
	sb t1, 59(t0)
	lbu t1, 8(a1)
	sb t1, 60(t0)
	lbu t1, 9(a1)
	sb t1, 61(t0)
	lbu t1, 10(a1)
	sb t1, 62(t0)
	lbu t1, 11(a1)
	sb t1, 63(t0)
	addi t1, zero, 0
	sd t1, 512(t0)
	sd t1, 520(t0)
	sd s8, 528(t0)
	sd s10, 536(t0)
	addi a0, t0, 0
	addi a1, a0, 64
	call {vg_chacha20_block}
	addi a1, a0, 64
	addi a0, a0, 384
	call {vg_poly1305_init}
	addi a1, zero, 0
	addi a2, s7, 0
	addi a3, s8, 0
	call {vg_poly1305_update}
	addi a1, s8, 0
	addi a3, zero, 0
	sub a3, a3, s8
	andi a3, a3, 15
	addi a2, a0, 128
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	addi a2, s9, 0
	addi a3, s10, 0
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	add a1, a1, s10
	addi a3, zero, 0
	sub a3, a3, s10
	andi a3, a3, 15
	addi a2, a0, 128
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	addi t0, s10, 15
	andi t0, t0, -16
	add a1, a1, t0
	addi a2, a0, 144
	addi a3, zero, 16
	call {vg_poly1305_update}
	addi a1, s8, 15
	andi a1, a1, -16
	addi t0, s10, 15
	andi t0, t0, -16
	add a1, a1, t0
	addi a1, a1, 16
	addi a2, a0, 160
	call {vg_poly1305_finalize}
	addi a0, a0, -384
	addi t0, zero, 1
	sb t0, 48(a0)
	addi a1, s9, 0
	addi a2, s10, 0
	addi a3, a0, 64
	call {vg_chacha20_xor}
	addi a0, a0, 384
	addi t0, a0, -384
	addi t1, zero, 0
	lbu t2, 544(t0)
	lbu t3, 0(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 545(t0)
	lbu t3, 1(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 546(t0)
	lbu t3, 2(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 547(t0)
	lbu t3, 3(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 548(t0)
	lbu t3, 4(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 549(t0)
	lbu t3, 5(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 550(t0)
	lbu t3, 6(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 551(t0)
	lbu t3, 7(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 552(t0)
	lbu t3, 8(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 553(t0)
	lbu t3, 9(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 554(t0)
	lbu t3, 10(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 555(t0)
	lbu t3, 11(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 556(t0)
	lbu t3, 12(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 557(t0)
	lbu t3, 13(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 558(t0)
	lbu t3, 14(s11)
	xor t2, t2, t3
	or t1, t1, t2
	lbu t2, 559(t0)
	lbu t3, 15(s11)
	xor t2, t2, t3
	or t1, t1, t2
	addi t2, zero, 1
	sltu t1, t1, t2
	ld s7, 560(t0)
	ld s8, 568(t0)
	ld s9, 576(t0)
	ld s10, 584(t0)
	ld s11, 592(t0)
	ld ra, 600(t0)
	addi a0, t1, 0
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
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	addi sp, sp, 624
	ret
	.option pop

vg_chacha20_poly1305_seal_gather:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	addi t5, sp, 16
	ld t5, 0(t5)
	addi t6, a6, 0
	beqz a5, 20f
22:
	lbu t0, 0(a4)
	lbu t3, 1(a4)
	slli t3, t3, 8
	or t0, t0, t3
	lbu t3, 2(a4)
	slli t3, t3, 16
	or t0, t0, t3
	lbu t3, 3(a4)
	slli t3, t3, 24
	or t0, t0, t3
	lbu t4, 4(a4)
	lbu t3, 5(a4)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(a4)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(a4)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t0, t0, t4
	lbu t1, 8(a4)
	lbu t3, 9(a4)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 10(a4)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 11(a4)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 12(a4)
	lbu t3, 13(a4)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 14(a4)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 15(a4)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	addi a4, a4, 16
	beqz t1, 23f
25:
	lbu t2, 0(t0)
	sb t2, 0(a6)
	addi t0, t0, 1
	addi a6, a6, 1
	addi t1, t1, -1
	bnez t1, 25b
	j 24f
23:
24:
	addi a5, a5, -1
	bnez a5, 22b
	j 21f
20:
21:
	addi a4, t6, 0
	addi a5, a7, 0
	addi a6, t5, 0
	call {vg_chacha20_poly1305_seal}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop
