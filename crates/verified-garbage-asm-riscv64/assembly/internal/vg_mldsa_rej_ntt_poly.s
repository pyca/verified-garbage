// The functions of `src/internal/vg_mldsa_rej_ntt_poly.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly:
	.option push
	.option arch, +m, +c
	sd s7, 2000(a2)
	sd s8, 2008(a2)
	sd s9, 2016(a2)
	sd s10, 2024(a2)
	sd s11, 2032(a2)
	sd ra, 2040(a2)
	addi s11, a2, 0
	addi s10, a1, 0
	addi s9, a0, 0
	addi s8, zero, 34
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
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s9, 0
	addi a4, s8, 0
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s11, 0
	addi a1, zero, 168
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s11, 0
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s11, 840
	addi a4, zero, 1008
	call {vg_keccak_squeeze}
	addi a0, s11, 840
	addi a1, s10, 0
	addi a2, zero, 0
	addi a3, zero, 336
	lui a4, 2046
	addi a4, a4, 1
20:
	lbu a5, 0(a0)
	lbu a6, 1(a0)
	lbu a7, 2(a0)
	slli a6, a6, 8
	slli a7, a7, 57
	srli a7, a7, 41
	add a7, a7, a6
	add a7, a7, a5
	sub t2, a7, a4
	srli t2, t2, 63
	addi t1, a2, -256
	srli t1, t1, 63
	and t2, t2, t1
	beqz t2, 21f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 22f
21:
22:
	addi a0, a0, 3
	addi a3, a3, -1
	bnez a3, 20b
	srli a0, a2, 8
	ld ra, 2040(s11)
	ld s7, 2000(s11)
	ld s8, 2008(s11)
	ld s9, 2016(s11)
	ld s10, 2024(s11)
	ld s11, 2032(s11)
	ret
	.option pop
