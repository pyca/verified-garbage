// The functions of `src/rsa_oaep_sha512_224_mgf1_sha512_224.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_precomputed:
	.option push
	.option arch, +m, +c
	addi sp, sp, -128
	addi t0, sp, 0
	sd s0, 16(t0)
	sd s1, 24(t0)
	sd s2, 32(t0)
	sd s3, 40(t0)
	sd s4, 48(t0)
	sd s5, 56(t0)
	sd s6, 64(t0)
	sd s7, 72(t0)
	sd s8, 80(t0)
	sd s9, 88(t0)
	sd s10, 96(t0)
	sd s11, 104(t0)
	sd ra, 112(t0)
	addi t6, sp, 128
	ld s0, 24(t6)
	addi s1, a3, 0
	addi s2, a0, 0
	addi s3, a4, 0
	addi s4, a5, 0
	addi s6, a6, 0
	addi s7, a7, 0
	ld t2, 0(t6)
	ld t3, 8(t6)
	ld t4, 16(t6)
	addi a0, zero, 58
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 20f
	addi a0, zero, 58
	sub a1, s1, a0
	sub a1, a1, t3
	srli a1, a1, 63
	srli a0, t3, 63
	or a0, a0, a1
	bnez a0, 22f
	addi a1, s0, 0
	addi t5, zero, 1024
	addi t0, zero, 0
24:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 24b
	addi a4, t4, 0
	addi a1, s0, 1
	addi a5, zero, 28
25:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 25b
	add a1, s0, s1
	sub a1, a1, t3
	addi a1, a1, -1
	addi t1, zero, 1
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a4, t2, 0
	addi a5, t3, 0
	bnez a5, 26f
	j 27f
26:
28:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 28b
27:
	addi a0, s0, 1024
	call {vg_sha512_224_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	call {vg_sha512_224_finalize}
	addi a4, s0, 1280
	addi a1, s0, 29
	addi a5, zero, 28
29:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 29b
	addi s6, s0, 1
	addi s7, zero, 28
	addi s8, s0, 29
	addi s9, s1, -29
	addi s10, zero, 0
	addi s11, zero, 0
210:
	addi a0, s0, 1024
	call {vg_sha512_224_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	call {vg_sha512_224_finalize}
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	addi a6, zero, 28
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
211:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 211b
	addi s10, s10, 1
	addi s11, s11, 28
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 210b
	addi s6, s0, 29
	addi s7, s1, -29
	addi s8, s0, 1
	addi s9, zero, 28
	addi s10, zero, 0
	addi s11, zero, 0
212:
	addi a0, s0, 1024
	call {vg_sha512_224_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
	addi a2, s0, 1344
	addi t1, s10, 0
	sb t1, 3(a2)
	srli t1, t1, 8
	sb t1, 2(a2)
	srli t1, t1, 8
	sb t1, 1(a2)
	srli t1, t1, 8
	sb t1, 0(a2)
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a3, zero, 4
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	call {vg_sha512_224_finalize}
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	addi a6, zero, 28
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
213:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 213b
	addi s10, s10, 1
	addi s11, s11, 28
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 212b
	addi t0, sp, 0
	addi t6, sp, 128
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 0(t0)
	ld t1, 32(t6)
	addi t1, t1, -1024
	sd t1, 8(t0)
	addi a0, s2, 0
	addi a1, s1, 0
	ld a2, 40(t6)
	ld a3, 48(t6)
	addi a4, s3, 0
	addi a5, s4, 0
	addi a6, s0, 0
	addi a7, s1, 0
	call {vg_rsa_public_precomputed_checked}
	j 23f
22:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
214:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 214b
	addi a0, zero, 0
23:
	j 21f
20:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
215:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 215b
	addi a0, zero, 0
21:
	addi t0, sp, 0
	ld s0, 16(t0)
	ld s1, 24(t0)
	ld s2, 32(t0)
	ld s3, 40(t0)
	ld s4, 48(t0)
	ld s5, 56(t0)
	ld s6, 64(t0)
	ld s7, 72(t0)
	ld s8, 80(t0)
	ld s9, 88(t0)
	ld s10, 96(t0)
	ld s11, 104(t0)
	ld ra, 112(t0)
	addi sp, sp, 128
	ret
	.option pop
