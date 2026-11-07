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
	addi a5, s0, 496
	srli a2, s3, 1
	addi a2, a2, -1
20:
	lwu a0, 1520(s0)
	lwu a1, 1524(s0)
	lwu a3, 1528(s0)
	sw s11, 0(a5)
	sw a0, 4(a5)
	sw a1, 8(a5)
	sw a3, 12(a5)
	addi s11, s11, 1
	addi a5, a5, 16
	addi a2, a2, -1
	bnez a2, 20b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1792
	call {vg_aes_encrypt_blocks}
	addi a5, s0, 496
	addi a1, s0, 16
21:
	ld a0, 0(a5)
	sd a0, 0(a1)
	addi a5, a5, 16
	addi a1, a1, 8
	addi s11, s11, -1
	bnez s11, 21b
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
	beqz a7, 22f
24:
	srli s11, s10, 10
	beqz s11, 25f
	addi s11, zero, 64
	j 26f
25:
	srli s11, s10, 4
26:
	addi a1, s0, 496
	addi a0, s11, 0
27:
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
	bnez a0, 27b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 24b
	j 23f
22:
23:
	beqz s10, 28f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
210:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 211f
	addi s11, zero, 64
	j 212f
211:
	srli s11, s10, 4
212:
	addi a1, s0, 496
	addi a0, s11, 0
213:
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
	bnez a0, 213b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 29f
28:
29:
	addi s9, s6, 0
	addi s10, s7, 0
	srli a7, s10, 4
	beqz a7, 214f
216:
	srli s11, s10, 10
	beqz s11, 217f
	addi s11, zero, 64
	j 218f
217:
	srli s11, s10, 4
218:
	addi a1, s0, 496
	addi a0, s11, 0
219:
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
	bnez a0, 219b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 216b
	j 215f
214:
215:
	beqz s10, 220f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
222:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 222b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 223f
	addi s11, zero, 64
	j 224f
223:
	srli s11, s10, 4
224:
	addi a1, s0, 496
	addi a0, s11, 0
225:
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
	bnez a0, 225b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 221f
220:
221:
	slli a0, s5, 3
	sd a0, 240(s0)
	slli a0, s7, 3
	sd a0, 248(s0)
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 226f
	addi s11, zero, 64
	j 227f
226:
	srli s11, s10, 4
227:
	addi a1, s0, 496
	addi a0, s11, 0
228:
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
	bnez a0, 228b
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
	addi a6, a3, 0
	call {vg_aes_ctr32_to}
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
	beqz a7, 229f
231:
	srli s11, s10, 10
	beqz s11, 232f
	addi s11, zero, 64
	j 233f
232:
	srli s11, s10, 4
233:
	addi a5, s0, 496
	addi a1, s11, 0
234:
	ld a2, 96(s0)
	ld a3, 104(s0)
	sd a2, 0(a5)
	sd a3, 8(a5)
	lwu a2, 96(s0)
	addi a2, a2, 1
	sw a2, 96(s0)
	addi a5, a5, 16
	addi a1, a1, -1
	bnez a1, 234b
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1792
	call {vg_aes_encrypt_blocks}
	addi a0, s0, 496
	addi a1, s9, 0
	slli a2, s11, 4
235:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 235b
	addi s9, a1, 0
	slli a2, s11, 4
	sub s10, s10, a2
	srli a7, s10, 4
	bnez a7, 231b
	j 230f
229:
230:
	beqz s10, 236f
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
	addi a6, a3, 0
	call {vg_aes_ctr32_to}
	addi a0, s0, 240
	addi a1, s9, 0
	addi a2, s10, 0
238:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 238b
	j 237f
236:
237:
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
	addi a5, s0, 496
	srli a2, s3, 1
	addi a2, a2, -1
20:
	lwu a0, 1520(s0)
	lwu a1, 1524(s0)
	lwu a3, 1528(s0)
	sw s11, 0(a5)
	sw a0, 4(a5)
	sw a1, 8(a5)
	sw a3, 12(a5)
	addi s11, s11, 1
	addi a5, a5, 16
	addi a2, a2, -1
	bnez a2, 20b
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1792
	call {vg_aes_encrypt_blocks}
	addi a5, s0, 496
	addi a1, s0, 16
21:
	ld a0, 0(a5)
	sd a0, 0(a1)
	addi a5, a5, 16
	addi a1, a1, 8
	addi s11, s11, -1
	bnez s11, 21b
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
	beqz a7, 22f
24:
	srli s11, s10, 10
	beqz s11, 25f
	addi s11, zero, 64
	j 26f
25:
	srli s11, s10, 4
26:
	addi a5, s0, 496
	addi a1, s11, 0
27:
	ld a2, 96(s0)
	ld a3, 104(s0)
	sd a2, 0(a5)
	sd a3, 8(a5)
	lwu a2, 96(s0)
	addi a2, a2, 1
	sw a2, 96(s0)
	addi a5, a5, 16
	addi a1, a1, -1
	bnez a1, 27b
	addi a0, s0, 256
	addi a1, s3, 0
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1792
	call {vg_aes_encrypt_blocks}
	addi a0, s0, 496
	addi a1, s9, 0
	slli a2, s11, 4
28:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 28b
	addi s9, a1, 0
	slli a2, s11, 4
	sub s10, s10, a2
	srli a7, s10, 4
	bnez a7, 24b
	j 23f
22:
23:
	beqz s10, 29f
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
	addi a6, a3, 0
	call {vg_aes_ctr32_to}
	addi a0, s0, 240
	addi a1, s9, 0
	addi a2, s10, 0
211:
	lbu t0, 0(a1)
	lbu a3, 0(a0)
	xor t0, t0, a3
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
	j 210f
29:
210:
	addi s9, s4, 0
	addi s10, s5, 0
	srli a7, s10, 4
	beqz a7, 212f
214:
	srli s11, s10, 10
	beqz s11, 215f
	addi s11, zero, 64
	j 216f
215:
	srli s11, s10, 4
216:
	addi a1, s0, 496
	addi a0, s11, 0
217:
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
	bnez a0, 217b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 214b
	j 213f
212:
213:
	beqz s10, 218f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
220:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 220b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 221f
	addi s11, zero, 64
	j 222f
221:
	srli s11, s10, 4
222:
	addi a1, s0, 496
	addi a0, s11, 0
223:
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
	bnez a0, 223b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 219f
218:
219:
	addi s9, s6, 0
	addi s10, s7, 0
	srli a7, s10, 4
	beqz a7, 224f
226:
	srli s11, s10, 10
	beqz s11, 227f
	addi s11, zero, 64
	j 228f
227:
	srli s11, s10, 4
228:
	addi a1, s0, 496
	addi a0, s11, 0
229:
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
	bnez a0, 229b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	bnez a7, 226b
	j 225f
224:
225:
	beqz s10, 230f
	addi t0, zero, 0
	sd t0, 240(s0)
	sd t0, 248(s0)
	addi a0, s9, 0
	addi a1, s0, 240
	addi a2, s10, 0
232:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 232b
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 233f
	addi s11, zero, 64
	j 234f
233:
	srli s11, s10, 4
234:
	addi a1, s0, 496
	addi a0, s11, 0
235:
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
	bnez a0, 235b
	slli a2, s11, 4
	sub s10, s10, a2
	addi a0, s0, 64
	addi a1, s0, 80
	addi a2, s0, 496
	addi a3, s11, 0
	addi a4, s0, 1536
	call {vg_ghash}
	srli a7, s10, 4
	j 231f
230:
231:
	slli a0, s5, 3
	sd a0, 240(s0)
	slli a0, s7, 3
	sd a0, 248(s0)
	addi s9, s0, 240
	addi s10, zero, 16
	srli s11, s10, 10
	beqz s11, 236f
	addi s11, zero, 64
	j 237f
236:
	srli s11, s10, 4
237:
	addi a1, s0, 496
	addi a0, s11, 0
238:
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
	bnez a0, 238b
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
	addi a6, a3, 0
	call {vg_aes_ctr32_to}
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
	beqz a1, 239f
241:
	lbu t0, 0(a0)
	and t0, t0, a2
	sb t0, 0(a0)
	addi a0, a0, 1
	addi a1, a1, -1
	bnez a1, 241b
	j 240f
239:
240:
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
