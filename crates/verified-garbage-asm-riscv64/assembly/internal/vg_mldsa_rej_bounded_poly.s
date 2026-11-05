// The functions of `src/internal/vg_mldsa_rej_bounded_poly.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly:
	.option push
	.option arch, +m, +c
	sd s7, 2000(a3)
	sd s8, 2008(a3)
	sd s9, 2016(a3)
	sd s10, 2024(a3)
	sd s11, 2032(a3)
	sd ra, 2040(a3)
	addi s11, a3, 0
	addi s10, a2, 0
	addi s9, a0, 0
	addi s8, zero, 66
	addi s7, a1, 0
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a0, s11, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s9, 0
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s11, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 840
	addi a4, zero, 272
	call {vg_keccak_squeeze}
	lui a6, 0
	addi a6, a6, 2
	subw a6, s7, a6
	beqz a6, 20f
	addi a0, s11, 840
	addi a1, s10, 0
	addi a2, zero, 0
	addi a3, zero, 272
	lui a4, 2046
	addi a4, a4, 1
22:
	lbu a5, 0(a0)
	slli a6, a5, 60
	srli a6, a6, 60
	addi t2, a6, -9
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a7, zero, 4
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 23f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 24f
23:
24:
	srli a6, a5, 4
	addi t2, a6, -9
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a7, zero, 4
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 25f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 26f
25:
26:
	addi a0, a0, 1
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
	addi a0, s11, 840
	addi a1, s10, 0
	addi a2, zero, 0
	addi a3, zero, 272
	lui a4, 2046
	addi a4, a4, 1
27:
	lbu a5, 0(a0)
	slli a6, a5, 60
	srli a6, a6, 60
	addi t2, a6, -15
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a6, a6, -10
	srli t1, a6, 63
	slli a7, t1, 3
	add a6, a6, a7
	slli a7, t1, 1
	add a6, a6, a7
	addi a6, a6, -5
	srli t1, a6, 63
	slli a7, t1, 2
	add a6, a6, a7
	add a6, a6, t1
	addi a7, zero, 2
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 28f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 29f
28:
29:
	srli a6, a5, 4
	addi t2, a6, -15
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a6, a6, -10
	srli t1, a6, 63
	slli a7, t1, 3
	add a6, a6, a7
	slli a7, t1, 1
	add a6, a6, a7
	addi a6, a6, -5
	srli t1, a6, 63
	slli a7, t1, 2
	add a6, a6, a7
	add a6, a6, t1
	addi a7, zero, 2
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 210f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 211f
210:
211:
	addi a0, a0, 1
	addi a3, a3, -1
	bnez a3, 27b
21:
	srli t0, a2, 8
	beqz t0, 212f
	j 213f
212:
	addi t0, zero, 0
	sd t0, 0(s11)
	sd t0, 8(s11)
	sd t0, 16(s11)
	sd t0, 24(s11)
	sd t0, 32(s11)
	sd t0, 40(s11)
	sd t0, 48(s11)
	sd t0, 56(s11)
	sd t0, 64(s11)
	sd t0, 72(s11)
	sd t0, 80(s11)
	sd t0, 88(s11)
	sd t0, 96(s11)
	sd t0, 104(s11)
	sd t0, 112(s11)
	sd t0, 120(s11)
	sd t0, 128(s11)
	sd t0, 136(s11)
	sd t0, 144(s11)
	sd t0, 152(s11)
	sd t0, 160(s11)
	sd t0, 168(s11)
	sd t0, 176(s11)
	sd t0, 184(s11)
	sd t0, 192(s11)
	addi a0, s11, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s9, 0
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 136
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s11, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s11, 840
	addi a4, zero, 544
	call {vg_keccak_squeeze}
	lui a6, 0
	addi a6, a6, 2
	subw a6, s7, a6
	beqz a6, 214f
	addi a0, s11, 840
	addi a1, s10, 0
	addi a2, zero, 0
	addi a3, zero, 544
	lui a4, 2046
	addi a4, a4, 1
216:
	lbu a5, 0(a0)
	slli a6, a5, 60
	srli a6, a6, 60
	addi t2, a6, -9
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a7, zero, 4
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 217f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 218f
217:
218:
	srli a6, a5, 4
	addi t2, a6, -9
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a7, zero, 4
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 219f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 220f
219:
220:
	addi a0, a0, 1
	addi a3, a3, -1
	bnez a3, 216b
	j 215f
214:
	addi a0, s11, 840
	addi a1, s10, 0
	addi a2, zero, 0
	addi a3, zero, 544
	lui a4, 2046
	addi a4, a4, 1
221:
	lbu a5, 0(a0)
	slli a6, a5, 60
	srli a6, a6, 60
	addi t2, a6, -15
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a6, a6, -10
	srli t1, a6, 63
	slli a7, t1, 3
	add a6, a6, a7
	slli a7, t1, 1
	add a6, a6, a7
	addi a6, a6, -5
	srli t1, a6, 63
	slli a7, t1, 2
	add a6, a6, a7
	add a6, a6, t1
	addi a7, zero, 2
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 222f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 223f
222:
223:
	srli a6, a5, 4
	addi t2, a6, -15
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	addi a6, a6, -10
	srli t1, a6, 63
	slli a7, t1, 3
	add a6, a6, a7
	slli a7, t1, 1
	add a6, a6, a7
	addi a6, a6, -5
	srli t1, a6, 63
	slli a7, t1, 2
	add a6, a6, a7
	add a6, a6, t1
	addi a7, zero, 2
	sub a7, a7, a6
	srli t1, a7, 63
	mul t1, t1, a4
	add a7, a7, t1
	beqz t2, 224f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 225f
224:
225:
	addi a0, a0, 1
	addi a3, a3, -1
	bnez a3, 221b
215:
213:
	srli a0, a2, 8
	ld ra, 2040(s11)
	ld s7, 2000(s11)
	ld s8, 2008(s11)
	ld s9, 2016(s11)
	ld s10, 2024(s11)
	ld s11, 2032(s11)
	ret
	.option pop
