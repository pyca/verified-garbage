// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -96
	addi t0, sp, 0
	sd s1, 16(t0)
	sd s2, 24(t0)
	sd s3, 32(t0)
	sd s4, 40(t0)
	sd ra, 48(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi t1, zero, 0
	sb t1, 72(t0)
	addi t1, zero, 2
	sb t1, 73(t0)
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t2, 0(t6)
	ld t3, 8(t6)
	addi t4, t0, 74
	addi t5, zero, 0
20:
	lbu t1, 0(t2)
	sb t1, 0(t4)
	addi t1, t1, -1
	srli t1, t1, 63
	or t5, t5, t1
	addi t2, t2, 1
	addi t4, t4, 1
	addi t3, t3, -1
	bnez t3, 20b
	addi t1, zero, 0
	sb t1, 0(t4)
	addi t4, t4, 1
	bnez a7, 21f
	j 22f
21:
	addi a4, a6, 0
	addi a1, t4, 0
	addi a5, a7, 0
23:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 23b
22:
	addi t0, sp, 0
	sd t5, 56(t0)
	addi a0, s1, 0
	addi a1, s2, 0
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, t0, 72
	addi a7, s2, 0
	addi t6, sp, 2032
	addi t6, t6, 96
	ld t1, 16(t6)
	sd t1, 0(t0)
	ld t1, 24(t6)
	sd t1, 8(t0)
	ld a2, 32(t6)
	ld a3, 40(t6)
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	ld a3, 56(t0)
	addi a3, a3, -1
	and a0, a0, a3
	addi a1, s1, 0
	addi a5, s2, 0
24:
	lbu t1, 0(a1)
	and t1, t1, a3
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 24b
	addi t0, sp, 0
	addi a1, t0, 72
	addi t5, s2, 0
	addi t0, zero, 0
25:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 25b
	addi t0, sp, 0
	ld s1, 16(t0)
	ld s2, 24(t0)
	ld s3, 32(t0)
	ld s4, 40(t0)
	ld ra, 48(t0)
	addi sp, sp, 96
	addi sp, sp, 2032
	ret
	.option pop
