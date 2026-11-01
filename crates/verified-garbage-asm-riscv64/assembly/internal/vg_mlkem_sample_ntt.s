// The functions of `src/internal/vg_mlkem_sample_ntt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	.option push
	.option arch, +m, +c
	sd s7, 1680(a2)
	sd s8, 1688(a2)
	sd s9, 1696(a2)
	sd ra, 1704(a2)
	addi s7, a0, 0
	addi s8, a1, 0
	addi s9, a2, 0
	addi t0, zero, 0
	sd t0, 0(s9)
	sd t0, 8(s9)
	sd t0, 16(s9)
	sd t0, 24(s9)
	sd t0, 32(s9)
	sd t0, 40(s9)
	sd t0, 48(s9)
	sd t0, 56(s9)
	sd t0, 64(s9)
	sd t0, 72(s9)
	sd t0, 80(s9)
	sd t0, 88(s9)
	sd t0, 96(s9)
	sd t0, 104(s9)
	sd t0, 112(s9)
	sd t0, 120(s9)
	sd t0, 128(s9)
	sd t0, 136(s9)
	sd t0, 144(s9)
	sd t0, 152(s9)
	sd t0, 160(s9)
	sd t0, 168(s9)
	sd t0, 176(s9)
	sd t0, 184(s9)
	sd t0, 192(s9)
	addi a0, s9, 0
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s7, 0
	addi a4, zero, 34
	call {vg_keccak_absorb}
	addi a2, a0, 0
	addi a0, s9, 0
	addi a1, zero, 168
	addi a3, zero, 31
	call {vg_keccak_pad}
	addi a0, s9, 0
	addi a1, zero, 168
	addi a2, zero, 0
	addi a3, s9, 840
	addi a4, zero, 840
	call {vg_keccak_squeeze}
	addi a0, s9, 840
	addi a1, s8, 0
	addi a2, zero, 0
	addi a3, zero, 280
	lui t3, 1
	addi t3, t3, -767
20:
	lbu a4, 0(a0)
	lbu a5, 1(a0)
	lbu a6, 2(a0)
	slli a7, a5, 60
	srli a7, a7, 52
	add a7, a4, a7
	srli t1, a5, 4
	slli t2, a6, 4
	add t1, t1, t2
	sub t2, a7, t3
	srli t2, t2, 63
	addi a4, a2, -256
	srli a4, a4, 63
	and t2, t2, a4
	beqz t2, 21f
	sw a7, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 22f
21:
22:
	sub t2, t1, t3
	srli t2, t2, 63
	addi a4, a2, -256
	srli a4, a4, 63
	and t2, t2, a4
	beqz t2, 23f
	sw t1, 0(a1)
	addi a1, a1, 4
	addi a2, a2, 1
	j 24f
23:
24:
	addi a0, a0, 3
	addi a3, a3, -1
	bnez a3, 20b
	srli a0, a2, 8
	ld ra, 1704(s9)
	ld s7, 1680(s9)
	ld s8, 1688(s9)
	ld s9, 1696(s9)
	ret
	.option pop
