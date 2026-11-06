// The functions of `src/internal/vg_rsa_private_checked.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 96(t0)
	sd s2, 104(t0)
	sd s3, 112(t0)
	sd s4, 120(t0)
	sd s5, 128(t0)
	sd s6, 136(t0)
	sd ra, 144(t0)
	addi s1, a0, 0
	addi s2, a2, 0
	addi s3, a3, 0
	addi s4, a4, 0
	addi s5, a5, 0
	addi s6, a6, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	addi a0, t0, 176
	addi a1, s3, 0
	addi a4, s6, 0
	addi a5, s3, 0
	ld a6, 0(t6)
	ld a7, 8(t6)
	ld t1, 16(t6)
	sd t1, 0(t0)
	ld t1, 24(t6)
	sd t1, 8(t0)
	ld t1, 32(t6)
	sd t1, 16(t0)
	ld t1, 40(t6)
	sd t1, 24(t0)
	ld t1, 48(t6)
	sd t1, 32(t0)
	ld t1, 56(t6)
	sd t1, 40(t0)
	ld t1, 64(t6)
	sd t1, 48(t0)
	ld t1, 72(t6)
	sd t1, 56(t0)
	ld t1, 80(t6)
	sd t1, 64(t0)
	ld t1, 88(t6)
	sd t1, 72(t0)
	call {vg_rsa_private_crt}
	addi t0, sp, 0
	sd a0, 152(t0)
	addi a0, t0, 1200
	addi a1, s3, 7
	srli a1, a1, 3
	slli a1, a1, 1
	addi a2, s2, 0
	addi a3, s3, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	ld a4, 80(t6)
	ld a5, 88(t6)
	call {vg_rsa_public_precompute}
	addi t0, sp, 0
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, t0, 1200
	addi a3, s3, 7
	srli a3, a3, 3
	slli a3, a3, 1
	addi a4, s4, 0
	addi a5, s5, 0
	addi a6, t0, 176
	addi a7, s3, 0
	addi t6, sp, 2032
	addi t6, t6, 1216
	ld t1, 80(t6)
	sd t1, 0(t0)
	ld t1, 88(t6)
	sd t1, 8(t0)
	call {vg_rsa_public_precomputed_checked}
	addi t0, sp, 0
	sd a0, 160(t0)
	addi t2, s1, 0
	addi t3, s6, 0
	addi t4, zero, 0
	addi t5, s3, 0
20:
	lbu a1, 0(t2)
	lbu a2, 0(t3)
	xor a1, a1, a2
	or t4, t4, a1
	addi t2, t2, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 20b
	addi t0, sp, 0
	ld a0, 152(t0)
	ld a1, 160(t0)
	and a0, a0, a1
	andi a0, a0, 1
	addi t4, t4, -1
	srli t4, t4, 63
	addi a1, zero, 2
	sub a1, a1, t4
	and t4, t4, a0
	addi a2, zero, 0
	sub a3, a2, t4
	sub a0, a2, a0
	and a0, a0, a1
	addi t5, s3, 0
	addi t2, s1, 0
	addi t3, t0, 176
21:
	lbu a1, 0(t3)
	and a1, a1, a3
	sb a1, 0(t2)
	addi a2, zero, 0
	sb a2, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 21b
	addi t0, sp, 0
	ld ra, 144(t0)
	ld s1, 96(t0)
	ld s2, 104(t0)
	ld s3, 112(t0)
	ld s4, 120(t0)
	ld s5, 128(t0)
	ld s6, 136(t0)
	addi sp, sp, 1216
	addi sp, sp, 2032
	ret
	.option pop
