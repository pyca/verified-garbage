// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1824
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t1, sp, 0
	ld t1, 0(t1)
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
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a3, 0
	addi s5, a4, 0
	addi s6, a5, 0
	addi s7, a6, 0
	addi s8, a7, 0
	lbu t0, 0(s1)
	sb t0, 1520(s0)
	lbu t0, 1(s1)
	sb t0, 1521(s0)
	lbu t0, 2(s1)
	sb t0, 1522(s0)
	lbu t0, 3(s1)
	sb t0, 1523(s0)
	lbu t0, 4(s1)
	sb t0, 1524(s0)
	lbu t0, 5(s1)
	sb t0, 1525(s0)
	lbu t0, 6(s1)
	sb t0, 1526(s0)
	lbu t0, 7(s1)
	sb t0, 1527(s0)
	lbu t0, 8(s1)
	sb t0, 1528(s0)
	lbu t0, 9(s1)
	sb t0, 1529(s0)
	lbu t0, 10(s1)
	sb t0, 1530(s0)
	lbu t0, 11(s1)
	sb t0, 1531(s0)
	addi s11, zero, 0
20:
	lwu a0, 1520(s0)
	lwu a1, 1524(s0)
	lwu a2, 1528(s0)
	sw s11, 112(s0)
	sw a0, 116(s0)
	sw a1, 120(s0)
	sw a2, 124(s0)
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 112
	addi a3, s0, 240
	addi a4, zero, 1
	addi a5, s0, 1792
	call {vg_aes_ctr32}
	ld a0, 240(s0)
	slli a1, s11, 3
	add a1, s0, a1
	sd a0, 16(a1)
	addi s11, s11, 1
	srli a2, s3, 1
	addi a2, a2, -1
	sub a2, a2, s11
	bnez a2, 20b
	addi a0, s0, 32
	addi a1, s3, -6
	slli a1, a1, 2
	addi a2, s0, 256
	addi a3, s0, 1792
	call {vg_aes_expand_key_scratch}
	ld a0, 16(s0)
	ld a1, 24(s0)
	andi a2, a0, 1
	addi a3, zero, 0
	sub a2, a3, a2
	srli a0, a0, 1
	slli a3, a1, 63
	or a0, a0, a3
	srli a1, a1, 1
	addi a3, zero, 225
	slli a3, a3, 56
	and a2, a2, a3
	xor a1, a1, a2
	srli t0, a1, 56
	sb t0, 64(s0)
	srli t0, a1, 48
	sb t0, 65(s0)
	srli t0, a1, 40
	sb t0, 66(s0)
	srli t0, a1, 32
	sb t0, 67(s0)
	srli t0, a1, 24
	sb t0, 68(s0)
	srli t0, a1, 16
	sb t0, 69(s0)
	srli t0, a1, 8
	sb t0, 70(s0)
	srli t0, a1, 0
	sb t0, 71(s0)
	srli t0, a0, 56
	sb t0, 72(s0)
	srli t0, a0, 48
	sb t0, 73(s0)
	srli t0, a0, 40
	sb t0, 74(s0)
	srli t0, a0, 32
	sb t0, 75(s0)
	srli t0, a0, 24
	sb t0, 76(s0)
	srli t0, a0, 16
	sb t0, 77(s0)
	srli t0, a0, 8
	sb t0, 78(s0)
	srli t0, a0, 0
	sb t0, 79(s0)
	addi t0, zero, 0
	sd t0, 80(s0)
	sd t0, 88(s0)
	addi s9, s4, 0
	addi s10, s5, 0
	srli a7, s10, 4
	beqz a7, 21f
23:
	srli s11, s10, 10
	beqz s11, 24f
	addi s11, zero, 64
	j 25f
24:
	srli s11, s10, 4
25:
	addi a1, s0, 496
	addi a0, s11, 0
26:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 26b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 23b
	j 22f
21:
22:
	beqz s10, 27f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
29:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 210f
	addi s11, zero, 64
	j 211f
210:
	srli s11, s10, 4
211:
	addi a1, s0, 496
	addi a0, s11, 0
212:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 212b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 28f
27:
28:
	addi s9, s6, 0
	addi s10, s7, 0
	srli a7, s10, 4
	beqz a7, 213f
215:
	srli s11, s10, 10
	beqz s11, 216f
	addi s11, zero, 64
	j 217f
216:
	srli s11, s10, 4
217:
	addi a1, s0, 496
	addi a0, s11, 0
218:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 218b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 215b
	j 214f
213:
214:
	beqz s10, 219f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
221:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 222f
	addi s11, zero, 64
	j 223f
222:
	srli s11, s10, 4
223:
	addi a1, s0, 496
	addi a0, s11, 0
224:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 224b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 220f
219:
220:
	slli a0, s5, 3
	sd a0, 240(s0)
	slli a0, s7, 3
	sd a0, 248(s0)
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 225f
	addi s11, zero, 64
	j 226f
225:
	srli s11, s10, 4
226:
	addi a1, s0, 496
	addi a0, s11, 0
227:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 227b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	lbu a0, 88(s0)
	slli a0, a0, 8
	lbu t0, 89(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 90(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 91(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 92(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 93(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 94(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 95(s0)
	or a0, a0, t0
	lbu a1, 80(s0)
	slli a1, a1, 8
	lbu t0, 81(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 82(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 83(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 84(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 85(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 86(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 87(s0)
	or a1, a1, t0
	ld a2, 1520(s0)
	xor a0, a0, a2
	lwu a2, 1528(s0)
	xor a1, a1, a2
	slli a1, a1, 1
	srli a1, a1, 1
	sd a0, 96(s0)
	sd a1, 104(s0)
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi t0, zero, 0
	sd t0, 0(s0)
	sd t0, 8(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s0, 0
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi s9, s6, 0
	addi s10, s7, 0
	ld a0, 0(s0)
	ld a1, 8(s0)
	addi a2, zero, 1
	slli a2, a2, 63
	or a1, a1, a2
	sd a0, 96(s0)
	sd a1, 104(s0)
	srli a7, s10, 4
	beqz a7, 228f
230:
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s9, 0
	addi a4, zero, 1
	call {vg_aes_ctr32}
	lwu a0, 96(s0)
	addi a0, a0, 1
	sw a0, 96(s0)
	addi s9, s9, 16
	addi s10, s10, -16
	srli a7, s10, 4
	bnez a7, 230b
	j 229f
228:
229:
	beqz s10, 231f
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s0, 240
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi a0, s0, 240
	addi a1, s9, 0
	addi a2, s10, 0
233:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 233b
	j 232f
231:
232:
	lbu t0, 0(s0)
	sb t0, 0(s8)
	lbu t0, 1(s0)
	sb t0, 1(s8)
	lbu t0, 2(s0)
	sb t0, 2(s8)
	lbu t0, 3(s0)
	sb t0, 3(s8)
	lbu t0, 4(s0)
	sb t0, 4(s8)
	lbu t0, 5(s0)
	sb t0, 5(s8)
	lbu t0, 6(s0)
	sb t0, 6(s8)
	lbu t0, 7(s0)
	sb t0, 7(s8)
	lbu t0, 8(s0)
	sb t0, 8(s8)
	lbu t0, 9(s0)
	sb t0, 9(s8)
	lbu t0, 10(s0)
	sb t0, 10(s8)
	lbu t0, 11(s0)
	sb t0, 11(s8)
	lbu t0, 12(s0)
	sb t0, 12(s8)
	lbu t0, 13(s0)
	sb t0, 13(s8)
	lbu t0, 14(s0)
	sb t0, 14(s8)
	lbu t0, 15(s0)
	sb t0, 15(s8)
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
	addi sp, sp, 1824
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_gcm_siv_open:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1824
	addi t0, sp, 0
	addi t1, t0, 8
	sd t1, 0(t0)
	addi t1, sp, 0
	ld t1, 0(t1)
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
	addi s1, a2, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a3, 0
	addi s5, a4, 0
	addi s6, a5, 0
	addi s7, a6, 0
	addi s8, a7, 0
	lbu t0, 0(s1)
	sb t0, 1520(s0)
	lbu t0, 1(s1)
	sb t0, 1521(s0)
	lbu t0, 2(s1)
	sb t0, 1522(s0)
	lbu t0, 3(s1)
	sb t0, 1523(s0)
	lbu t0, 4(s1)
	sb t0, 1524(s0)
	lbu t0, 5(s1)
	sb t0, 1525(s0)
	lbu t0, 6(s1)
	sb t0, 1526(s0)
	lbu t0, 7(s1)
	sb t0, 1527(s0)
	lbu t0, 8(s1)
	sb t0, 1528(s0)
	lbu t0, 9(s1)
	sb t0, 1529(s0)
	lbu t0, 10(s1)
	sb t0, 1530(s0)
	lbu t0, 11(s1)
	sb t0, 1531(s0)
	lbu t0, 0(s8)
	sb t0, 0(s0)
	lbu t0, 1(s8)
	sb t0, 1(s0)
	lbu t0, 2(s8)
	sb t0, 2(s0)
	lbu t0, 3(s8)
	sb t0, 3(s0)
	lbu t0, 4(s8)
	sb t0, 4(s0)
	lbu t0, 5(s8)
	sb t0, 5(s0)
	lbu t0, 6(s8)
	sb t0, 6(s0)
	lbu t0, 7(s8)
	sb t0, 7(s0)
	lbu t0, 8(s8)
	sb t0, 8(s0)
	lbu t0, 9(s8)
	sb t0, 9(s0)
	lbu t0, 10(s8)
	sb t0, 10(s0)
	lbu t0, 11(s8)
	sb t0, 11(s0)
	lbu t0, 12(s8)
	sb t0, 12(s0)
	lbu t0, 13(s8)
	sb t0, 13(s0)
	lbu t0, 14(s8)
	sb t0, 14(s0)
	lbu t0, 15(s8)
	sb t0, 15(s0)
	addi s11, zero, 0
20:
	lwu a0, 1520(s0)
	lwu a1, 1524(s0)
	lwu a2, 1528(s0)
	sw s11, 112(s0)
	sw a0, 116(s0)
	sw a1, 120(s0)
	sw a2, 124(s0)
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 112
	addi a3, s0, 240
	addi a4, zero, 1
	addi a5, s0, 1792
	call {vg_aes_ctr32}
	ld a0, 240(s0)
	slli a1, s11, 3
	add a1, s0, a1
	sd a0, 16(a1)
	addi s11, s11, 1
	srli a2, s3, 1
	addi a2, a2, -1
	sub a2, a2, s11
	bnez a2, 20b
	addi a0, s0, 32
	addi a1, s3, -6
	slli a1, a1, 2
	addi a2, s0, 256
	addi a3, s0, 1792
	call {vg_aes_expand_key_scratch}
	ld a0, 16(s0)
	ld a1, 24(s0)
	andi a2, a0, 1
	addi a3, zero, 0
	sub a2, a3, a2
	srli a0, a0, 1
	slli a3, a1, 63
	or a0, a0, a3
	srli a1, a1, 1
	addi a3, zero, 225
	slli a3, a3, 56
	and a2, a2, a3
	xor a1, a1, a2
	srli t0, a1, 56
	sb t0, 64(s0)
	srli t0, a1, 48
	sb t0, 65(s0)
	srli t0, a1, 40
	sb t0, 66(s0)
	srli t0, a1, 32
	sb t0, 67(s0)
	srli t0, a1, 24
	sb t0, 68(s0)
	srli t0, a1, 16
	sb t0, 69(s0)
	srli t0, a1, 8
	sb t0, 70(s0)
	srli t0, a1, 0
	sb t0, 71(s0)
	srli t0, a0, 56
	sb t0, 72(s0)
	srli t0, a0, 48
	sb t0, 73(s0)
	srli t0, a0, 40
	sb t0, 74(s0)
	srli t0, a0, 32
	sb t0, 75(s0)
	srli t0, a0, 24
	sb t0, 76(s0)
	srli t0, a0, 16
	sb t0, 77(s0)
	srli t0, a0, 8
	sb t0, 78(s0)
	srli t0, a0, 0
	sb t0, 79(s0)
	addi t0, zero, 0
	sd t0, 80(s0)
	sd t0, 88(s0)
	addi s9, s6, 0
	addi s10, s7, 0
	ld a0, 0(s0)
	ld a1, 8(s0)
	addi a2, zero, 1
	slli a2, a2, 63
	or a1, a1, a2
	sd a0, 96(s0)
	sd a1, 104(s0)
	srli a7, s10, 4
	beqz a7, 21f
23:
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s9, 0
	addi a4, zero, 1
	call {vg_aes_ctr32}
	lwu a0, 96(s0)
	addi a0, a0, 1
	sw a0, 96(s0)
	addi s9, s9, 16
	addi s10, s10, -16
	srli a7, s10, 4
	bnez a7, 23b
	j 22f
21:
22:
	beqz s10, 24f
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s0, 240
	addi a4, zero, 1
	call {vg_aes_ctr32}
	addi a0, s0, 240
	addi a1, s9, 0
	addi a2, s10, 0
26:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 26b
	j 25f
24:
25:
	addi s9, s4, 0
	addi s10, s5, 0
	srli a7, s10, 4
	beqz a7, 27f
29:
	srli s11, s10, 10
	beqz s11, 210f
	addi s11, zero, 64
	j 211f
210:
	srli s11, s10, 4
211:
	addi a1, s0, 496
	addi a0, s11, 0
212:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 212b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 29b
	j 28f
27:
28:
	beqz s10, 213f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 216f
	addi s11, zero, 64
	j 217f
216:
	srli s11, s10, 4
217:
	addi a1, s0, 496
	addi a0, s11, 0
218:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 218b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 214f
213:
214:
	addi s9, s6, 0
	addi s10, s7, 0
	srli a7, s10, 4
	beqz a7, 219f
221:
	srli s11, s10, 10
	beqz s11, 222f
	addi s11, zero, 64
	j 223f
222:
	srli s11, s10, 4
223:
	addi a1, s0, 496
	addi a0, s11, 0
224:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 224b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 221b
	j 220f
219:
220:
	beqz s10, 225f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
227:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 227b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 228f
	addi s11, zero, 64
	j 229f
228:
	srli s11, s10, 4
229:
	addi a1, s0, 496
	addi a0, s11, 0
230:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 230b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 226f
225:
226:
	slli a0, s5, 3
	sd a0, 240(s0)
	slli a0, s7, 3
	sd a0, 248(s0)
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 231f
	addi s11, zero, 64
	j 232f
231:
	srli s11, s10, 4
232:
	addi a1, s0, 496
	addi a0, s11, 0
233:
	lbu a2, 8(s9)
	slli a2, a2, 8
	lbu t0, 9(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 10(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 11(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 12(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 13(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 14(s9)
	or a2, a2, t0
	slli a2, a2, 8
	lbu t0, 15(s9)
	or a2, a2, t0
	lbu a3, 0(s9)
	slli a3, a3, 8
	lbu t0, 1(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 2(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 3(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 4(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 5(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 6(s9)
	or a3, a3, t0
	slli a3, a3, 8
	lbu t0, 7(s9)
	or a3, a3, t0
	sd a2, 0(a1)
	sd a3, 8(a1)
	addi s9, s9, 16
	addi a1, a1, 16
	addi a0, a0, -1
	bnez a0, 233b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	lbu a0, 88(s0)
	slli a0, a0, 8
	lbu t0, 89(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 90(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 91(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 92(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 93(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 94(s0)
	or a0, a0, t0
	slli a0, a0, 8
	lbu t0, 95(s0)
	or a0, a0, t0
	lbu a1, 80(s0)
	slli a1, a1, 8
	lbu t0, 81(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 82(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 83(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 84(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 85(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 86(s0)
	or a1, a1, t0
	slli a1, a1, 8
	lbu t0, 87(s0)
	or a1, a1, t0
	ld a2, 1520(s0)
	xor a0, a0, a2
	lwu a2, 1528(s0)
	xor a1, a1, a2
	slli a1, a1, 1
	srli a1, a1, 1
	sd a0, 96(s0)
	sd a1, 104(s0)
	ld a0, 96(s0)
	ld a1, 104(s0)
	sd a0, 112(s0)
	sd a1, 120(s0)
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 112
	addi a5, s0, 1792
	addi a3, s0, 240
	addi a4, zero, 1
	call {vg_aes_ctr32}
	ld a0, 0(s0)
	ld a1, 240(s0)
	xor a0, a0, a1
	ld a1, 8(s0)
	ld a2, 248(s0)
	xor a1, a1, a2
	or a0, a0, a1
	addi a1, zero, 0
	sub a1, a1, a0
	or a0, a0, a1
	srli a0, a0, 63
	addi s11, zero, 1
	sub s11, s11, a0
	addi a2, zero, 0
	sub a2, a2, s11
	addi a0, s6, 0
	addi a1, s7, 0
	beqz a1, 234f
236:
	lbu t0, 0(a0)
	and t0, t0, a2
	sb t0, 0(a0)
	addi a0, a0, 1
	addi a1, a1, -1
	bnez a1, 236b
	j 235f
234:
235:
	addi a0, s11, 0
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
	addi sp, sp, 1824
	addi sp, sp, 2032
	ret
	.option pop
