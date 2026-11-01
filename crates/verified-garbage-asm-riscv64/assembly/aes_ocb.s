// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a3, sp, 0
	sd s0, 128(a3)
	sd s1, 136(a3)
	sd s2, 144(a3)
	sd s3, 152(a3)
	sd s4, 160(a3)
	sd s5, 168(a3)
	sd s6, 176(a3)
	sd s7, 184(a3)
	sd s8, 192(a3)
	sd s9, 200(a3)
	sd s10, 208(a3)
	sd s11, 216(a3)
	sd ra, 224(a3)
	addi s0, a3, 0
	addi s2, a2, 0
	srli s3, a1, 2
	addi s3, s3, 6
	addi a3, s0, 512
	call {vg_aes_expand_key_scratch}
	addi t0, zero, 0
	sd t0, 240(s2)
	sd t0, 248(s2)
	sd t0, 96(s0)
	sd t0, 104(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 96
	addi a3, s2, 240
	addi a4, zero, 1
	addi a5, s0, 512
	call {vg_aes_ctr32}
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_ocb_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -560
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 560(t1)
	sd t1, 0(t0)
	addi t1, t0, 2032
	ld t1, 568(t1)
	sd t1, 8(t0)
	addi t1, t0, 24
	sd t1, 16(t0)
	addi t1, sp, 0
	ld t1, 16(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s1, s0, 16
	addi s4, a2, 0
	addi s5, a3, 0
	addi s7, a3, 0
	sd a4, 232(s0)
	addi s10, a5, 0
	sd a6, 240(s0)
	addi s11, a7, 0
	addi t1, sp, 0
	ld s9, 0(t1)
	ld s8, 8(t1)
	lbu t1, 240(s2)
	slli t1, t1, 8
	lbu t0, 241(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 242(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 243(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 244(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 245(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 246(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 247(s2)
	or t1, t1, t0
	lbu t2, 248(s2)
	slli t2, t2, 8
	lbu t0, 249(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 250(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 251(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 252(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 253(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 254(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 255(s2)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 64(s0)
	srli t0, t1, 48
	sb t0, 65(s0)
	srli t0, t1, 40
	sb t0, 66(s0)
	srli t0, t1, 32
	sb t0, 67(s0)
	srli t0, t1, 24
	sb t0, 68(s0)
	srli t0, t1, 16
	sb t0, 69(s0)
	srli t0, t1, 8
	sb t0, 70(s0)
	srli t0, t1, 0
	sb t0, 71(s0)
	srli t0, t2, 56
	sb t0, 72(s0)
	srli t0, t2, 48
	sb t0, 73(s0)
	srli t0, t2, 40
	sb t0, 74(s0)
	srli t0, t2, 32
	sb t0, 75(s0)
	srli t0, t2, 24
	sb t0, 76(s0)
	srli t0, t2, 16
	sb t0, 77(s0)
	srli t0, t2, 8
	sb t0, 78(s0)
	srli t0, t2, 0
	sb t0, 79(s0)
	lbu t1, 64(s0)
	slli t1, t1, 8
	lbu t0, 65(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 66(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 67(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 68(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 69(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 70(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 71(s0)
	or t1, t1, t0
	lbu t2, 72(s0)
	slli t2, t2, 8
	lbu t0, 73(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 74(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 75(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 76(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 77(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 78(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 79(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 80(s0)
	srli t0, t1, 48
	sb t0, 81(s0)
	srli t0, t1, 40
	sb t0, 82(s0)
	srli t0, t1, 32
	sb t0, 83(s0)
	srli t0, t1, 24
	sb t0, 84(s0)
	srli t0, t1, 16
	sb t0, 85(s0)
	srli t0, t1, 8
	sb t0, 86(s0)
	srli t0, t1, 0
	sb t0, 87(s0)
	srli t0, t2, 56
	sb t0, 88(s0)
	srli t0, t2, 48
	sb t0, 89(s0)
	srli t0, t2, 40
	sb t0, 90(s0)
	srli t0, t2, 32
	sb t0, 91(s0)
	srli t0, t2, 24
	sb t0, 92(s0)
	srli t0, t2, 16
	sb t0, 93(s0)
	srli t0, t2, 8
	sb t0, 94(s0)
	srli t0, t2, 0
	sb t0, 95(s0)
	addi t0, zero, 0
	sd t0, 32(s0)
	sd t0, 40(s0)
	addi t0, zero, 0
	sd t0, 112(s0)
	sd t0, 120(s0)
	addi a1, s0, 127
	sub a1, a1, s5
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a0, s4, 0
	addi a2, s5, 0
20:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	andi t1, s8, 15
	slli t1, t1, 4
	lbu t2, 112(s0)
	or t2, t2, t1
	sb t2, 112(s0)
	lbu t2, 127(s0)
	andi t1, t2, 63
	sd t1, 288(s0)
	andi t2, t2, 192
	sb t2, 127(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	lbu t1, 112(s0)
	slli t1, t1, 8
	lbu t0, 113(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 114(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 115(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 116(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 117(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 118(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 119(s0)
	or t1, t1, t0
	lbu t2, 120(s0)
	slli t2, t2, 8
	lbu t0, 121(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 122(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 123(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 124(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 125(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 126(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 127(s0)
	or t2, t2, t0
	slli t3, t1, 8
	srli t6, t2, 56
	or t3, t3, t6
	xor t3, t3, t1
	ld t4, 288(s0)
	andi t5, t4, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 1
	srli a6, t2, 63
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 1
	srli a6, t3, 63
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 1
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 1
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 2
	srli a6, t2, 62
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 2
	srli a6, t3, 62
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 2
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 2
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 4
	srli a6, t2, 60
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 4
	srli a6, t3, 60
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 4
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 3
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 8
	srli a6, t2, 56
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 8
	srli a6, t3, 56
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 8
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 4
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 16
	srli a6, t2, 48
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 16
	srli a6, t3, 48
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 16
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 5
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 32
	srli a6, t2, 32
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 32
	srli a6, t3, 32
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 32
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t0, t1, 56
	sb t0, 16(s0)
	srli t0, t1, 48
	sb t0, 17(s0)
	srli t0, t1, 40
	sb t0, 18(s0)
	srli t0, t1, 32
	sb t0, 19(s0)
	srli t0, t1, 24
	sb t0, 20(s0)
	srli t0, t1, 16
	sb t0, 21(s0)
	srli t0, t1, 8
	sb t0, 22(s0)
	srli t0, t1, 0
	sb t0, 23(s0)
	srli t0, t2, 56
	sb t0, 24(s0)
	srli t0, t2, 48
	sb t0, 25(s0)
	srli t0, t2, 40
	sb t0, 26(s0)
	srli t0, t2, 32
	sb t0, 27(s0)
	srli t0, t2, 24
	sb t0, 28(s0)
	srli t0, t2, 16
	sb t0, 29(s0)
	srli t0, t2, 8
	sb t0, 30(s0)
	srli t0, t2, 0
	sb t0, 31(s0)
	srli t0, t1, 56
	sb t0, 320(s0)
	srli t0, t1, 48
	sb t0, 321(s0)
	srli t0, t1, 40
	sb t0, 322(s0)
	srli t0, t1, 32
	sb t0, 323(s0)
	srli t0, t1, 24
	sb t0, 324(s0)
	srli t0, t1, 16
	sb t0, 325(s0)
	srli t0, t1, 8
	sb t0, 326(s0)
	srli t0, t1, 0
	sb t0, 327(s0)
	srli t0, t2, 56
	sb t0, 328(s0)
	srli t0, t2, 48
	sb t0, 329(s0)
	srli t0, t2, 40
	sb t0, 330(s0)
	srli t0, t2, 32
	sb t0, 331(s0)
	srli t0, t2, 24
	sb t0, 332(s0)
	srli t0, t2, 16
	sb t0, 333(s0)
	srli t0, t2, 8
	sb t0, 334(s0)
	srli t0, t2, 0
	sb t0, 335(s0)
	addi t0, zero, 0
	sd t0, 48(s0)
	sd t0, 56(s0)
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	ld s4, 232(s0)
	srli t1, s10, 4
	sd t1, 304(s0)
	addi s6, zero, 1
	beqz t1, 21f
23:
	ld t1, 304(s0)
	srli t2, t1, 3
	beqz t2, 24f
	addi s5, zero, 8
	j 25f
24:
	addi s5, t1, 0
25:
	sd s5, 296(s0)
	ld t1, 304(s0)
	sub t1, t1, s5
	sd t1, 304(s0)
	addi a7, s0, 384
26:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 27f
	j 28f
27:
29:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 29b
28:
	ld t1, 272(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 272(s0)
	ld t1, 280(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 280(s0)
	addi a0, s4, 0
	addi a1, a7, 0
	addi a2, zero, 16
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	ld t1, 0(a7)
	ld t2, 272(s0)
	xor t1, t1, t2
	sd t1, 0(a7)
	ld t1, 8(a7)
	ld t2, 280(s0)
	xor t1, t1, t2
	sd t1, 8(a7)
	addi a7, a7, 16
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 26b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 384
	ld a3, 296(s0)
	call {vg_aes_encrypt_blocks}
	addi a7, s0, 384
	ld s5, 296(s0)
211:
	ld t1, 48(s0)
	ld t2, 0(a7)
	xor t1, t1, t2
	sd t1, 48(s0)
	ld t1, 56(s0)
	ld t2, 8(a7)
	xor t1, t1, t2
	sd t1, 56(s0)
	addi a7, a7, 16
	addi s5, s5, -1
	bnez s5, 211b
	ld t1, 304(s0)
	bnez t1, 23b
	j 22f
21:
22:
	andi s5, s10, 15
	beqz s5, 212f
	ld t1, 272(s0)
	ld t2, 240(s2)
	xor t1, t1, t2
	sd t1, 272(s0)
	ld t1, 280(s0)
	ld t2, 248(s2)
	xor t1, t1, t2
	sd t1, 280(s0)
	addi t0, zero, 0
	sd t0, 384(s0)
	sd t0, 392(s0)
	addi a1, s0, 384
	addi a0, s4, 0
	addi a2, s5, 0
214:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	addi t1, zero, 128
	sb t1, 0(a1)
	ld t1, 384(s0)
	ld t2, 272(s0)
	xor t1, t1, t2
	sd t1, 384(s0)
	ld t1, 392(s0)
	ld t2, 280(s0)
	xor t1, t1, t2
	sd t1, 392(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 384
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	ld t1, 48(s0)
	ld t2, 384(s0)
	xor t1, t1, t2
	sd t1, 48(s0)
	ld t1, 56(s0)
	ld t2, 392(s0)
	xor t1, t1, t2
	sd t1, 56(s0)
	j 213f
212:
213:
	srli t1, s11, 4
	beqz t1, 215f
	ld s4, 240(s0)
	srli s5, s11, 4
	addi s6, zero, 1
217:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 218f
	j 219f
218:
220:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 220b
219:
	ld t1, 16(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 24(s0)
	addi a0, s4, 0
	addi a1, s0, 256
	addi a2, zero, 16
221:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	ld t1, 32(s0)
	ld t2, 256(s0)
	xor t1, t1, t2
	sd t1, 32(s0)
	ld t1, 40(s0)
	ld t2, 264(s0)
	xor t1, t1, t2
	sd t1, 40(s0)
	addi a0, s0, 16
	addi a1, s4, 0
	addi a2, zero, 16
222:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 217b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	ld a2, 240(s0)
	srli a3, s11, 4
	call {vg_aes_encrypt_blocks}
	ld t1, 320(s0)
	ld t2, 328(s0)
	sd t1, 16(s0)
	sd t2, 24(s0)
	ld s4, 240(s0)
	srli s5, s11, 4
	addi s6, zero, 1
223:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 224f
	j 225f
224:
226:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 226b
225:
	ld t1, 16(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 24(s0)
	addi a0, s0, 16
	addi a1, s4, 0
	addi a2, zero, 16
227:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 223b
	j 216f
215:
216:
	andi s5, s11, 15
	sub s4, s11, s5
	ld t1, 240(s0)
	add s4, s4, t1
	beqz s5, 228f
	ld t1, 16(s0)
	ld t2, 240(s2)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 248(s2)
	xor t1, t1, t2
	sd t1, 24(s0)
	ld t1, 16(s0)
	ld t2, 24(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a1, s0, 256
	addi a0, s4, 0
	addi a2, s5, 0
230:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 230b
	addi t1, zero, 128
	sb t1, 0(a1)
	ld t1, 32(s0)
	ld t2, 256(s0)
	xor t1, t1, t2
	sd t1, 32(s0)
	ld t1, 40(s0)
	ld t2, 264(s0)
	xor t1, t1, t2
	sd t1, 40(s0)
	addi a0, s0, 112
	addi a1, s4, 0
	addi a2, s5, 0
231:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 231b
	j 229f
228:
229:
	ld t1, 32(s0)
	ld t2, 40(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	ld t1, 112(s0)
	ld t2, 16(s0)
	xor t1, t1, t2
	sd t1, 112(s0)
	ld t1, 120(s0)
	ld t2, 24(s0)
	xor t1, t1, t2
	sd t1, 120(s0)
	ld t1, 112(s0)
	ld t2, 64(s0)
	xor t1, t1, t2
	sd t1, 112(s0)
	ld t1, 120(s0)
	ld t2, 72(s0)
	xor t1, t1, t2
	sd t1, 120(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	ld t1, 112(s0)
	ld t2, 120(s0)
	sd t1, 0(s0)
	sd t2, 8(s0)
	ld t1, 0(s0)
	ld t2, 48(s0)
	xor t1, t1, t2
	sd t1, 0(s0)
	ld t1, 8(s0)
	ld t2, 56(s0)
	xor t1, t1, t2
	sd t1, 8(s0)
	addi a0, s0, 0
	addi a1, s9, 0
	addi a2, s8, 0
232:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 232b
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 560
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_ocb_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -560
	addi t0, sp, 0
	addi t1, t0, 2032
	ld t1, 560(t1)
	sd t1, 0(t0)
	addi t1, t0, 2032
	ld t1, 568(t1)
	sd t1, 8(t0)
	addi t1, t0, 24
	sd t1, 16(t0)
	addi t1, sp, 0
	ld t1, 16(t1)
	sd s0, 128(t1)
	sd s1, 136(t1)
	sd s2, 144(t1)
	sd s3, 152(t1)
	sd s4, 160(t1)
	sd s5, 168(t1)
	sd s6, 176(t1)
	sd s7, 184(t1)
	sd s8, 192(t1)
	sd s9, 200(t1)
	sd s10, 208(t1)
	sd s11, 216(t1)
	sd ra, 224(t1)
	addi s0, t1, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s1, s0, 16
	addi s4, a2, 0
	addi s5, a3, 0
	addi s7, a3, 0
	sd a4, 232(s0)
	addi s10, a5, 0
	sd a6, 240(s0)
	addi s11, a7, 0
	addi t1, sp, 0
	ld s9, 0(t1)
	ld s8, 8(t1)
	lbu t1, 240(s2)
	slli t1, t1, 8
	lbu t0, 241(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 242(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 243(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 244(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 245(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 246(s2)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 247(s2)
	or t1, t1, t0
	lbu t2, 248(s2)
	slli t2, t2, 8
	lbu t0, 249(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 250(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 251(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 252(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 253(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 254(s2)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 255(s2)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 64(s0)
	srli t0, t1, 48
	sb t0, 65(s0)
	srli t0, t1, 40
	sb t0, 66(s0)
	srli t0, t1, 32
	sb t0, 67(s0)
	srli t0, t1, 24
	sb t0, 68(s0)
	srli t0, t1, 16
	sb t0, 69(s0)
	srli t0, t1, 8
	sb t0, 70(s0)
	srli t0, t1, 0
	sb t0, 71(s0)
	srli t0, t2, 56
	sb t0, 72(s0)
	srli t0, t2, 48
	sb t0, 73(s0)
	srli t0, t2, 40
	sb t0, 74(s0)
	srli t0, t2, 32
	sb t0, 75(s0)
	srli t0, t2, 24
	sb t0, 76(s0)
	srli t0, t2, 16
	sb t0, 77(s0)
	srli t0, t2, 8
	sb t0, 78(s0)
	srli t0, t2, 0
	sb t0, 79(s0)
	lbu t1, 64(s0)
	slli t1, t1, 8
	lbu t0, 65(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 66(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 67(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 68(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 69(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 70(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 71(s0)
	or t1, t1, t0
	lbu t2, 72(s0)
	slli t2, t2, 8
	lbu t0, 73(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 74(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 75(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 76(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 77(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 78(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 79(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 80(s0)
	srli t0, t1, 48
	sb t0, 81(s0)
	srli t0, t1, 40
	sb t0, 82(s0)
	srli t0, t1, 32
	sb t0, 83(s0)
	srli t0, t1, 24
	sb t0, 84(s0)
	srli t0, t1, 16
	sb t0, 85(s0)
	srli t0, t1, 8
	sb t0, 86(s0)
	srli t0, t1, 0
	sb t0, 87(s0)
	srli t0, t2, 56
	sb t0, 88(s0)
	srli t0, t2, 48
	sb t0, 89(s0)
	srli t0, t2, 40
	sb t0, 90(s0)
	srli t0, t2, 32
	sb t0, 91(s0)
	srli t0, t2, 24
	sb t0, 92(s0)
	srli t0, t2, 16
	sb t0, 93(s0)
	srli t0, t2, 8
	sb t0, 94(s0)
	srli t0, t2, 0
	sb t0, 95(s0)
	addi t0, zero, 0
	sd t0, 32(s0)
	sd t0, 40(s0)
	addi t0, zero, 0
	sd t0, 112(s0)
	sd t0, 120(s0)
	addi a1, s0, 127
	sub a1, a1, s5
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a0, s4, 0
	addi a2, s5, 0
20:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	andi t1, s8, 15
	slli t1, t1, 4
	lbu t2, 112(s0)
	or t2, t2, t1
	sb t2, 112(s0)
	lbu t2, 127(s0)
	andi t1, t2, 63
	sd t1, 288(s0)
	andi t2, t2, 192
	sb t2, 127(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	lbu t1, 112(s0)
	slli t1, t1, 8
	lbu t0, 113(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 114(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 115(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 116(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 117(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 118(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 119(s0)
	or t1, t1, t0
	lbu t2, 120(s0)
	slli t2, t2, 8
	lbu t0, 121(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 122(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 123(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 124(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 125(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 126(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 127(s0)
	or t2, t2, t0
	slli t3, t1, 8
	srli t6, t2, 56
	or t3, t3, t6
	xor t3, t3, t1
	ld t4, 288(s0)
	andi t5, t4, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 1
	srli a6, t2, 63
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 1
	srli a6, t3, 63
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 1
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 1
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 2
	srli a6, t2, 62
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 2
	srli a6, t3, 62
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 2
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 2
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 4
	srli a6, t2, 60
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 4
	srli a6, t3, 60
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 4
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 3
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 8
	srli a6, t2, 56
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 8
	srli a6, t3, 56
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 8
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 4
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 16
	srli a6, t2, 48
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 16
	srli a6, t3, 48
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 16
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t5, t4, 5
	andi t5, t5, 1
	addi t6, zero, 0
	sub t5, t6, t5
	slli t6, t1, 32
	srli a6, t2, 32
	or t6, t6, a6
	xor t6, t6, t1
	and t6, t6, t5
	xor t1, t1, t6
	slli t6, t2, 32
	srli a6, t3, 32
	or t6, t6, a6
	xor t6, t6, t2
	and t6, t6, t5
	xor t2, t2, t6
	slli t6, t3, 32
	xor t6, t6, t3
	and t6, t6, t5
	xor t3, t3, t6
	srli t0, t1, 56
	sb t0, 16(s0)
	srli t0, t1, 48
	sb t0, 17(s0)
	srli t0, t1, 40
	sb t0, 18(s0)
	srli t0, t1, 32
	sb t0, 19(s0)
	srli t0, t1, 24
	sb t0, 20(s0)
	srli t0, t1, 16
	sb t0, 21(s0)
	srli t0, t1, 8
	sb t0, 22(s0)
	srli t0, t1, 0
	sb t0, 23(s0)
	srli t0, t2, 56
	sb t0, 24(s0)
	srli t0, t2, 48
	sb t0, 25(s0)
	srli t0, t2, 40
	sb t0, 26(s0)
	srli t0, t2, 32
	sb t0, 27(s0)
	srli t0, t2, 24
	sb t0, 28(s0)
	srli t0, t2, 16
	sb t0, 29(s0)
	srli t0, t2, 8
	sb t0, 30(s0)
	srli t0, t2, 0
	sb t0, 31(s0)
	srli t0, t1, 56
	sb t0, 320(s0)
	srli t0, t1, 48
	sb t0, 321(s0)
	srli t0, t1, 40
	sb t0, 322(s0)
	srli t0, t1, 32
	sb t0, 323(s0)
	srli t0, t1, 24
	sb t0, 324(s0)
	srli t0, t1, 16
	sb t0, 325(s0)
	srli t0, t1, 8
	sb t0, 326(s0)
	srli t0, t1, 0
	sb t0, 327(s0)
	srli t0, t2, 56
	sb t0, 328(s0)
	srli t0, t2, 48
	sb t0, 329(s0)
	srli t0, t2, 40
	sb t0, 330(s0)
	srli t0, t2, 32
	sb t0, 331(s0)
	srli t0, t2, 24
	sb t0, 332(s0)
	srli t0, t2, 16
	sb t0, 333(s0)
	srli t0, t2, 8
	sb t0, 334(s0)
	srli t0, t2, 0
	sb t0, 335(s0)
	addi t0, zero, 0
	sd t0, 48(s0)
	sd t0, 56(s0)
	addi t0, zero, 0
	sd t0, 272(s0)
	sd t0, 280(s0)
	ld s4, 232(s0)
	srli t1, s10, 4
	sd t1, 304(s0)
	addi s6, zero, 1
	beqz t1, 21f
23:
	ld t1, 304(s0)
	srli t2, t1, 3
	beqz t2, 24f
	addi s5, zero, 8
	j 25f
24:
	addi s5, t1, 0
25:
	sd s5, 296(s0)
	ld t1, 304(s0)
	sub t1, t1, s5
	sd t1, 304(s0)
	addi a7, s0, 384
26:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 27f
	j 28f
27:
29:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 29b
28:
	ld t1, 272(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 272(s0)
	ld t1, 280(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 280(s0)
	addi a0, s4, 0
	addi a1, a7, 0
	addi a2, zero, 16
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	ld t1, 0(a7)
	ld t2, 272(s0)
	xor t1, t1, t2
	sd t1, 0(a7)
	ld t1, 8(a7)
	ld t2, 280(s0)
	xor t1, t1, t2
	sd t1, 8(a7)
	addi a7, a7, 16
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 26b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 384
	ld a3, 296(s0)
	call {vg_aes_encrypt_blocks}
	addi a7, s0, 384
	ld s5, 296(s0)
211:
	ld t1, 48(s0)
	ld t2, 0(a7)
	xor t1, t1, t2
	sd t1, 48(s0)
	ld t1, 56(s0)
	ld t2, 8(a7)
	xor t1, t1, t2
	sd t1, 56(s0)
	addi a7, a7, 16
	addi s5, s5, -1
	bnez s5, 211b
	ld t1, 304(s0)
	bnez t1, 23b
	j 22f
21:
22:
	andi s5, s10, 15
	beqz s5, 212f
	ld t1, 272(s0)
	ld t2, 240(s2)
	xor t1, t1, t2
	sd t1, 272(s0)
	ld t1, 280(s0)
	ld t2, 248(s2)
	xor t1, t1, t2
	sd t1, 280(s0)
	addi t0, zero, 0
	sd t0, 384(s0)
	sd t0, 392(s0)
	addi a1, s0, 384
	addi a0, s4, 0
	addi a2, s5, 0
214:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
	addi t1, zero, 128
	sb t1, 0(a1)
	ld t1, 384(s0)
	ld t2, 272(s0)
	xor t1, t1, t2
	sd t1, 384(s0)
	ld t1, 392(s0)
	ld t2, 280(s0)
	xor t1, t1, t2
	sd t1, 392(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 384
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	ld t1, 48(s0)
	ld t2, 384(s0)
	xor t1, t1, t2
	sd t1, 48(s0)
	ld t1, 56(s0)
	ld t2, 392(s0)
	xor t1, t1, t2
	sd t1, 56(s0)
	j 213f
212:
213:
	srli t1, s11, 4
	beqz t1, 215f
	ld s4, 240(s0)
	srli s5, s11, 4
	addi s6, zero, 1
217:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 218f
	j 219f
218:
220:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 220b
219:
	ld t1, 16(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 24(s0)
	addi a0, s0, 16
	addi a1, s4, 0
	addi a2, zero, 16
221:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 217b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	ld a2, 240(s0)
	srli a3, s11, 4
	call {vg_aes_decrypt_blocks}
	ld t1, 320(s0)
	ld t2, 328(s0)
	sd t1, 16(s0)
	sd t2, 24(s0)
	ld s4, 240(s0)
	srli s5, s11, 4
	addi s6, zero, 1
222:
	ld t1, 80(s0)
	ld t2, 88(s0)
	sd t1, 96(s0)
	sd t2, 104(s0)
	addi a5, s6, 0
	andi t3, a5, 1
	beqz t3, 223f
	j 224f
223:
225:
	lbu t1, 96(s0)
	slli t1, t1, 8
	lbu t0, 97(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 98(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 99(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 100(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 101(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 102(s0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 103(s0)
	or t1, t1, t0
	lbu t2, 104(s0)
	slli t2, t2, 8
	lbu t0, 105(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 106(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 107(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 108(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 109(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 110(s0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 111(s0)
	or t2, t2, t0
	srli t3, t1, 63
	addi t4, zero, 0
	sub t3, t4, t3
	addi t4, zero, 135
	and t3, t3, t4
	slli t1, t1, 1
	srli t4, t2, 63
	or t1, t1, t4
	slli t2, t2, 1
	xor t2, t2, t3
	srli t0, t1, 56
	sb t0, 96(s0)
	srli t0, t1, 48
	sb t0, 97(s0)
	srli t0, t1, 40
	sb t0, 98(s0)
	srli t0, t1, 32
	sb t0, 99(s0)
	srli t0, t1, 24
	sb t0, 100(s0)
	srli t0, t1, 16
	sb t0, 101(s0)
	srli t0, t1, 8
	sb t0, 102(s0)
	srli t0, t1, 0
	sb t0, 103(s0)
	srli t0, t2, 56
	sb t0, 104(s0)
	srli t0, t2, 48
	sb t0, 105(s0)
	srli t0, t2, 40
	sb t0, 106(s0)
	srli t0, t2, 32
	sb t0, 107(s0)
	srli t0, t2, 24
	sb t0, 108(s0)
	srli t0, t2, 16
	sb t0, 109(s0)
	srli t0, t2, 8
	sb t0, 110(s0)
	srli t0, t2, 0
	sb t0, 111(s0)
	srli a5, a5, 1
	andi t3, a5, 1
	beqz t3, 225b
224:
	ld t1, 16(s0)
	ld t2, 96(s0)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 104(s0)
	xor t1, t1, t2
	sd t1, 24(s0)
	addi a0, s0, 16
	addi a1, s4, 0
	addi a2, zero, 16
226:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 226b
	addi a0, s4, 0
	addi a1, s0, 256
	addi a2, zero, 16
227:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	ld t1, 32(s0)
	ld t2, 256(s0)
	xor t1, t1, t2
	sd t1, 32(s0)
	ld t1, 40(s0)
	ld t2, 264(s0)
	xor t1, t1, t2
	sd t1, 40(s0)
	addi s4, s4, 16
	addi s6, s6, 1
	addi s5, s5, -1
	bnez s5, 222b
	j 216f
215:
216:
	andi s5, s11, 15
	sub s4, s11, s5
	ld t1, 240(s0)
	add s4, s4, t1
	beqz s5, 228f
	ld t1, 16(s0)
	ld t2, 240(s2)
	xor t1, t1, t2
	sd t1, 16(s0)
	ld t1, 24(s0)
	ld t2, 248(s2)
	xor t1, t1, t2
	sd t1, 24(s0)
	ld t1, 16(s0)
	ld t2, 24(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	addi a0, s0, 112
	addi a1, s4, 0
	addi a2, s5, 0
230:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 230b
	addi t0, zero, 0
	sd t0, 256(s0)
	sd t0, 264(s0)
	addi a1, s0, 256
	addi a0, s4, 0
	addi a2, s5, 0
231:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 231b
	addi t1, zero, 128
	sb t1, 0(a1)
	ld t1, 32(s0)
	ld t2, 256(s0)
	xor t1, t1, t2
	sd t1, 32(s0)
	ld t1, 40(s0)
	ld t2, 264(s0)
	xor t1, t1, t2
	sd t1, 40(s0)
	j 229f
228:
229:
	ld t1, 32(s0)
	ld t2, 40(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	ld t1, 112(s0)
	ld t2, 16(s0)
	xor t1, t1, t2
	sd t1, 112(s0)
	ld t1, 120(s0)
	ld t2, 24(s0)
	xor t1, t1, t2
	sd t1, 120(s0)
	ld t1, 112(s0)
	ld t2, 64(s0)
	xor t1, t1, t2
	sd t1, 112(s0)
	ld t1, 120(s0)
	ld t2, 72(s0)
	xor t1, t1, t2
	sd t1, 120(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a4, s0, 512
	addi a2, s0, 112
	addi a3, zero, 1
	call {vg_aes_encrypt_blocks}
	ld t1, 112(s0)
	ld t2, 120(s0)
	sd t1, 256(s0)
	sd t2, 264(s0)
	ld t1, 256(s0)
	ld t2, 48(s0)
	xor t1, t1, t2
	sd t1, 256(s0)
	ld t1, 264(s0)
	ld t2, 56(s0)
	xor t1, t1, t2
	sd t1, 264(s0)
	addi t0, zero, 0
	sd t0, 0(s0)
	sd t0, 8(s0)
	addi a0, s9, 0
	addi a1, s0, 0
	addi a2, s8, 0
232:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 232b
	addi t0, zero, 0
	sd t0, 336(s0)
	sd t0, 344(s0)
	addi a0, s0, 256
	addi a1, s0, 336
	addi a2, s8, 0
233:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 233b
	ld t1, 0(s0)
	ld t2, 336(s0)
	xor t1, t1, t2
	ld t2, 8(s0)
	ld t3, 344(s0)
	xor t2, t2, t3
	or t1, t1, t2
	addi t2, zero, 0
	sltu t1, t2, t1
	addi a0, zero, 1
	sub a0, a0, t1
	ld s4, 240(s0)
	addi s5, s11, 0
	addi t2, zero, 0
	sub t5, t2, a0
	beqz s5, 234f
236:
	lbu t2, 0(s4)
	and t2, t2, t5
	sb t2, 0(s4)
	addi s4, s4, 1
	addi s5, s5, -1
	bnez s5, 236b
	j 235f
234:
235:
	addi t1, s0, 0
	ld s0, 128(t1)
	ld s1, 136(t1)
	ld s2, 144(t1)
	ld s3, 152(t1)
	ld s4, 160(t1)
	ld s5, 168(t1)
	ld s6, 176(t1)
	ld s7, 184(t1)
	ld s8, 192(t1)
	ld s9, 200(t1)
	ld s10, 208(t1)
	ld s11, 216(t1)
	ld ra, 224(t1)
	addi sp, sp, 560
	addi sp, sp, 2032
	ret
	.option pop
