// The functions of `src/aes_ofb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb:
	.option push
	.option arch, +m, +c
	addi t0, a5, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	sd ra, 16(t0)
	sd s1, 24(t0)
	addi s1, a5, 0
	call {vg_aes_ofb_chain}
	addi t0, s1, 2047
	addi t0, t0, 8
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s1, 24(t0)
	ret
	.option pop

vg_aes_ofb_final:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi a6, sp, 0
	sd ra, 0(a6)
	sd s1, 8(a6)
	sd s2, 16(a6)
	sd s3, 24(a6)
	sd s4, 32(a6)
	sd s5, 40(a6)
	sd s6, 48(a6)
	sd s7, 56(a6)
	addi s1, a0, 0
	addi s4, a1, 0
	addi s5, a2, 0
	addi s6, a5, 0
	addi s7, a6, 0
	srli t0, a4, 4
	slli t1, t0, 4
	add s2, a3, t1
	sub s3, a4, t1
	addi a4, t0, 0
	call {vg_aes_ofb}
	beqz s3, 20f
	addi a0, s1, 0
	addi a1, s4, 0
	addi a2, s5, 0
	addi a3, zero, 1
	addi a4, s6, 0
	call {vg_aes_encrypt_blocks}
	addi t2, s5, 0
22:
	lbu t0, 0(s2)
	lbu t1, 0(t2)
	xor t0, t0, t1
	sb t0, 0(s2)
	addi s2, s2, 1
	addi t2, t2, 1
	addi s3, s3, -1
	bnez s3, 22b
	j 21f
20:
21:
	ld ra, 0(s7)
	ld s1, 8(s7)
	ld s2, 16(s7)
	ld s3, 24(s7)
	ld s4, 32(s7)
	ld s5, 40(s7)
	ld s6, 48(s7)
	ld s7, 56(s7)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	addi sp, sp, 64
	ret
	.option pop
