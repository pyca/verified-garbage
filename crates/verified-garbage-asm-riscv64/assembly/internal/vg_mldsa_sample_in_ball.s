// The functions of `src/internal/vg_mldsa_sample_in_ball.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball:
	.option push
	.option arch, +m, +c
	sd s7, 2000(a4)
	sd s8, 2008(a4)
	sd s9, 2016(a4)
	sd s10, 2024(a4)
	sd s11, 2032(a4)
	sd ra, 2040(a4)
	addi s11, a4, 0
	addi s10, a3, 0
	addi s9, a0, 0
	addi s8, a1, 0
	addi s7, a2, 0
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
	addi t2, zero, 0
	addi a1, s10, 0
	addi a3, zero, 256
20:
	sw t2, 0(a1)
	addi a1, a1, 4
	addi a3, a3, -1
	bnez a3, 20b
	ld a6, 840(s11)
	addi a2, zero, 256
	subw a2, a2, s7
	slli a1, a2, 2
	add a1, s10, a1
	addi a0, s11, 848
	addi a3, zero, 264
	lui a4, 2046
	addi a4, a4, -1
21:
	addi t2, a2, -256
	srli t2, t2, 63
	beqz t2, 22f
	lbu a5, 0(a0)
	sub t1, a2, a5
	srli t1, t1, 63
	beqz t1, 24f
	j 25f
24:
	slli a7, a5, 2
	add a7, s10, a7
	lwu t1, 0(a7)
	sw t1, 0(a1)
	slli t2, a6, 63
	srli t2, t2, 63
	mul t2, t2, a4
	addi t2, t2, 1
	sw t2, 0(a7)
	srli a6, a6, 1
	addi a1, a1, 4
	addi a2, a2, 1
25:
	j 23f
22:
23:
	addi a0, a0, 1
	addi a3, a3, -1
	bnez a3, 21b
	srli a0, a2, 8
	ld ra, 2040(s11)
	ld s7, 2000(s11)
	ld s8, 2008(s11)
	ld s9, 2016(s11)
	ld s10, 2024(s11)
	ld s11, 2032(s11)
	ret
	.option pop
