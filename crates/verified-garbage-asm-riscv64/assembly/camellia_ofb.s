// The functions of `src/camellia_ofb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ofb:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -18
	beqz t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -1232
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 22f
	beqz s3, 24f
26:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 816(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 820(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 824(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 828(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 26b
	j 25f
24:
25:
	j 23f
22:
	beqz s3, 27f
29:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 29b
	j 28f
27:
28:
23:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 408
210:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 210b
	addi sp, sp, 1232
	addi sp, sp, 2032
	j 21f
20:
	addi sp, sp, -2032
	addi sp, sp, -1232
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 211f
	beqz s3, 213f
215:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 816(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 820(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 824(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 828(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 215b
	j 214f
213:
214:
	j 212f
211:
	beqz s3, 216f
218:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 218b
	j 217f
216:
217:
212:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 408
219:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 219b
	addi sp, sp, 1232
	addi sp, sp, 2032
21:
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -1216
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	addi sp, sp, 1216
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_camellia_ofb_final:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -18
	beqz t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -1232
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 22f
	beqz s3, 24f
26:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t0, zero, 16
	bltu s3, t0, 27f
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 816(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 820(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 824(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 828(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 28f
27:
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	addi t2, s4, 816
29:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 29b
28:
	bnez s3, 26b
	j 25f
24:
25:
	j 23f
22:
	beqz s3, 210f
212:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_24}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t0, zero, 16
	bltu s3, t0, 213f
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 214f
213:
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	addi t2, s4, 816
215:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 215b
214:
	bnez s3, 212b
	j 211f
210:
211:
23:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 408
216:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 216b
	addi sp, sp, 1232
	addi sp, sp, 2032
	j 21f
20:
	addi sp, sp, -2032
	addi sp, sp, -1232
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 32(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 36(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 40(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sw t0, 44(s4)
	addi s2, a2, 0
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_prepare_encrypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	andi t0, s2, 3
	beqz t0, 217f
	beqz s3, 219f
221:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t0, zero, 16
	bltu s3, t0, 222f
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 816(s4)
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 820(s4)
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 824(s4)
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lwu t1, 828(s4)
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 223f
222:
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	addi t2, s4, 816
224:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 224b
223:
	bnez s3, 221b
	j 220f
219:
220:
	j 218f
217:
	beqz s3, 225f
227:
	lwu t0, 32(s4)
	sw t0, 816(s4)
	lwu t0, 36(s4)
	sw t0, 820(s4)
	lwu t0, 40(s4)
	sw t0, 824(s4)
	lwu t0, 44(s4)
	sw t0, 828(s4)
	addi t6, s4, 2032
	addi t6, t6, 1216
	sd ra, 0(t6)
	call {vg_camellia_modes_crypt_18}
	addi t6, s4, 2032
	addi t6, t6, 1216
	ld ra, 0(t6)
	addi t0, zero, 16
	bltu s3, t0, 228f
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	lwu t0, 0(s2)
	lwu t1, 816(s4)
	xor t0, t0, t1
	sw t0, 0(s2)
	lwu t0, 4(s2)
	lwu t1, 820(s4)
	xor t0, t0, t1
	sw t0, 4(s2)
	lwu t0, 8(s2)
	lwu t1, 824(s4)
	xor t0, t0, t1
	sw t0, 8(s2)
	lwu t0, 12(s2)
	lwu t1, 828(s4)
	xor t0, t0, t1
	sw t0, 12(s2)
	addi s2, s2, 16
	addi s3, s3, -16
	j 229f
228:
	lwu t0, 816(s4)
	sw t0, 32(s4)
	lwu t0, 820(s4)
	sw t0, 36(s4)
	lwu t0, 824(s4)
	sw t0, 40(s4)
	lwu t0, 828(s4)
	sw t0, 44(s4)
	addi t2, s4, 816
230:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 230b
229:
	bnez s3, 227b
	j 226f
225:
226:
218:
	addi s2, s1, 0
	lwu t0, 32(s4)
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lwu t0, 36(s4)
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lwu t0, 40(s4)
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lwu t0, 44(s4)
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 408
231:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 231b
	addi sp, sp, 1232
	addi sp, sp, 2032
21:
	addi t0, zero, 0
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	sd t0, 1216(t1)
	sd t0, 1224(t1)
	sd t0, 1232(t1)
	sd t0, 1240(t1)
	sd t0, 1248(t1)
	sd t0, 1256(t1)
	sd t0, 1264(t1)
	sd t0, 1272(t1)
	sd t0, 1280(t1)
	sd t0, 1288(t1)
	sd t0, 1296(t1)
	sd t0, 1304(t1)
	sd t0, 1312(t1)
	sd t0, 1320(t1)
	sd t0, 1328(t1)
	sd t0, 1336(t1)
	sd t0, 1344(t1)
	sd t0, 1352(t1)
	sd t0, 1360(t1)
	sd t0, 1368(t1)
	sd t0, 1376(t1)
	sd t0, 1384(t1)
	sd t0, 1392(t1)
	sd t0, 1400(t1)
	sd t0, 1408(t1)
	sd t0, 1416(t1)
	sd t0, 1424(t1)
	sd t0, 1432(t1)
	sd t0, 1440(t1)
	sd t0, 1448(t1)
	sd t0, 1456(t1)
	sd t0, 1464(t1)
	sd t0, 1472(t1)
	sd t0, 1480(t1)
	sd t0, 1488(t1)
	sd t0, 1496(t1)
	sd t0, 1504(t1)
	sd t0, 1512(t1)
	sd t0, 1520(t1)
	sd t0, 1528(t1)
	sd t0, 1536(t1)
	sd t0, 1544(t1)
	sd t0, 1552(t1)
	sd t0, 1560(t1)
	sd t0, 1568(t1)
	sd t0, 1576(t1)
	sd t0, 1584(t1)
	sd t0, 1592(t1)
	sd t0, 1600(t1)
	sd t0, 1608(t1)
	sd t0, 1616(t1)
	sd t0, 1624(t1)
	sd t0, 1632(t1)
	sd t0, 1640(t1)
	sd t0, 1648(t1)
	sd t0, 1656(t1)
	sd t0, 1664(t1)
	sd t0, 1672(t1)
	sd t0, 1680(t1)
	sd t0, 1688(t1)
	sd t0, 1696(t1)
	sd t0, 1704(t1)
	sd t0, 1712(t1)
	sd t0, 1720(t1)
	sd t0, 1728(t1)
	sd t0, 1736(t1)
	sd t0, 1744(t1)
	sd t0, 1752(t1)
	sd t0, 1760(t1)
	sd t0, 1768(t1)
	sd t0, 1776(t1)
	sd t0, 1784(t1)
	sd t0, 1792(t1)
	sd t0, 1800(t1)
	sd t0, 1808(t1)
	sd t0, 1816(t1)
	sd t0, 1824(t1)
	sd t0, 1832(t1)
	sd t0, 1840(t1)
	sd t0, 1848(t1)
	sd t0, 1856(t1)
	sd t0, 1864(t1)
	sd t0, 1872(t1)
	sd t0, 1880(t1)
	sd t0, 1888(t1)
	sd t0, 1896(t1)
	sd t0, 1904(t1)
	sd t0, 1912(t1)
	sd t0, 1920(t1)
	sd t0, 1928(t1)
	sd t0, 1936(t1)
	sd t0, 1944(t1)
	sd t0, 1952(t1)
	sd t0, 1960(t1)
	sd t0, 1968(t1)
	sd t0, 1976(t1)
	sd t0, 1984(t1)
	sd t0, 1992(t1)
	sd t0, 2000(t1)
	sd t0, 2008(t1)
	sd t0, 2016(t1)
	sd t0, 2024(t1)
	sd t0, 2032(t1)
	sd t0, 2040(t1)
	addi sp, sp, -1216
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	sd t0, 1056(t1)
	sd t0, 1064(t1)
	sd t0, 1072(t1)
	sd t0, 1080(t1)
	sd t0, 1088(t1)
	sd t0, 1096(t1)
	sd t0, 1104(t1)
	sd t0, 1112(t1)
	sd t0, 1120(t1)
	sd t0, 1128(t1)
	sd t0, 1136(t1)
	sd t0, 1144(t1)
	sd t0, 1152(t1)
	sd t0, 1160(t1)
	sd t0, 1168(t1)
	sd t0, 1176(t1)
	sd t0, 1184(t1)
	sd t0, 1192(t1)
	sd t0, 1200(t1)
	sd t0, 1208(t1)
	addi sp, sp, 1216
	addi sp, sp, 16
	addi sp, sp, 2032
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
