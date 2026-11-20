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
	call {vg_aes_ctr32}
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
	addi sp, sp, -1808
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
	addi sp, sp, 1808
	addi sp, sp, 16
	addi sp, sp, 2032
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
	call {vg_aes_ctr32}
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
	addi sp, sp, -1808
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
	addi sp, sp, 1808
	addi sp, sp, 16
	addi sp, sp, 2032
	addi sp, sp, 16
	addi sp, sp, 2032
	slli a0, a0, 32
	srli a0, a0, 32
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
