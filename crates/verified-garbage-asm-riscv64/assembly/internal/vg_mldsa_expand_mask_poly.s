// The functions of `src/internal/vg_mldsa_expand_mask_poly.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly:
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
	addi a4, zero, 640
	call {vg_keccak_squeeze}
	lui a6, 32
	addi a6, a6, 0
	subw a6, s7, a6
	beqz a6, 20f
	addi a7, s11, 840
	addi t1, s10, 0
	lui a4, 2046
	addi a4, a4, 1
	lui a1, 128
	addi a1, a1, 0
	addi t2, zero, 128
22:
	addi a5, zero, 0
	lbu a6, 0(a7)
	add a5, a5, a6
	lbu a6, 1(a7)
	slli a6, a6, 8
	add a5, a5, a6
	lbu a6, 2(a7)
	slli a6, a6, 16
	add a5, a5, a6
	slli a6, a5, 44
	srli a6, a6, 44
	srli a5, a5, 20
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 0(t1)
	lbu a6, 3(a7)
	slli a6, a6, 4
	add a5, a5, a6
	lbu a6, 4(a7)
	slli a6, a6, 12
	add a5, a5, a6
	slli a6, a5, 44
	srli a6, a6, 44
	srli a5, a5, 20
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 4(t1)
	addi a7, a7, 5
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 22b
	j 21f
20:
	addi a7, s11, 840
	addi t1, s10, 0
	lui a4, 2046
	addi a4, a4, 1
	lui a1, 32
	addi a1, a1, 0
	addi t2, zero, 64
23:
	addi a5, zero, 0
	lbu a6, 0(a7)
	add a5, a5, a6
	lbu a6, 1(a7)
	slli a6, a6, 8
	add a5, a5, a6
	lbu a6, 2(a7)
	slli a6, a6, 16
	add a5, a5, a6
	slli a6, a5, 46
	srli a6, a6, 46
	srli a5, a5, 18
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 0(t1)
	lbu a6, 3(a7)
	slli a6, a6, 6
	add a5, a5, a6
	lbu a6, 4(a7)
	slli a6, a6, 14
	add a5, a5, a6
	slli a6, a5, 46
	srli a6, a6, 46
	srli a5, a5, 18
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 4(t1)
	lbu a6, 5(a7)
	slli a6, a6, 4
	add a5, a5, a6
	lbu a6, 6(a7)
	slli a6, a6, 12
	add a5, a5, a6
	slli a6, a5, 46
	srli a6, a6, 46
	srli a5, a5, 18
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 8(t1)
	lbu a6, 7(a7)
	slli a6, a6, 2
	add a5, a5, a6
	lbu a6, 8(a7)
	slli a6, a6, 10
	add a5, a5, a6
	slli a6, a5, 46
	srli a6, a6, 46
	srli a5, a5, 18
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	sw a6, 12(t1)
	addi a7, a7, 9
	addi t1, t1, 16
	addi t2, t2, -1
	bnez t2, 23b
21:
	ld ra, 2040(s11)
	ld s7, 2000(s11)
	ld s8, 2008(s11)
	ld s9, 2016(s11)
	ld s10, 2024(s11)
	ld s11, 2032(s11)
	ret
	.option pop
