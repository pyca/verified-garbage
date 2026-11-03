// The functions of `src/rsa_oaep_sha384_mgf1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha384_mgf1_decrypt:
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
	ld s0, 104(t6)
	addi s1, a4, 0
	addi s2, a0, 0
	addi s3, a2, 0
	addi sp, sp, -96
	addi t0, sp, 0
	addi t6, sp, 224
	sd a7, 0(t0)
	ld t1, 0(t6)
	sd t1, 8(t0)
	ld t1, 8(t6)
	sd t1, 16(t0)
	ld t1, 16(t6)
	sd t1, 24(t0)
	ld t1, 24(t6)
	sd t1, 32(t0)
	ld t1, 32(t6)
	sd t1, 40(t0)
	ld t1, 40(t6)
	sd t1, 48(t0)
	ld t1, 48(t6)
	sd t1, 56(t0)
	ld t1, 56(t6)
	sd t1, 64(t0)
	ld t1, 64(t6)
	sd t1, 72(t0)
	addi t1, zero, 1024
	slli t1, t1, 3
	add t1, s0, t1
	sd t1, 80(t0)
	ld t1, 112(t6)
	addi t1, t1, -1024
	sd t1, 88(t0)
	addi a2, a3, 0
	addi a3, s1, 0
	addi a4, a5, 0
	addi a5, a6, 0
	ld a6, 88(t6)
	addi a7, s1, 0
	addi a0, s0, 0
	addi a1, s1, 0
	call {vg_rsa_private_checked}
	addi sp, sp, 96
	slli s4, a0, 32
	srli s4, s4, 32
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 20f
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
22:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
23:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 23b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 22b
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
	addi s10, zero, 0
	addi s11, zero, 0
24:
	addi a0, s0, 1024
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
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
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 248
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
	sub t2, t1, a6
	srli t3, t2, 63
	addi t4, zero, 0
	sub t3, t4, t3
	and t2, t2, t3
	add a6, a6, t2
25:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t2, t2, t1
	sb t2, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 25b
	addi t1, sp, 248
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 24b
	addi a0, s0, 1024
	call {vg_sha384_init}
	addi t6, sp, 128
	addi a0, s0, 1024
	addi a1, zero, 0
	ld a2, 72(t6)
	ld a3, 80(t6)
	call {vg_sha512_update}
	addi t6, sp, 128
	addi a0, s0, 1024
	ld a1, 80(t6)
	addi a2, s0, 1280
	call {vg_sha384_finalize}
	addi a4, s0, 49
	addi a5, s0, 1280
	lbu s5, 0(s0)
	addi a6, zero, 48
26:
	lbu t1, 0(a4)
	lbu t2, 0(a5)
	xor t1, t1, t2
	or s5, s5, t1
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 26b
	addi a1, s0, 97
	addi a2, s1, -97
	addi a3, zero, 0
	addi a4, zero, 0
	addi a4, a4, -1
	addi s6, zero, 0
27:
	lbu a7, 0(a1)
	addi t1, a7, -1
	srli t1, t1, 63
	addi t2, zero, 1
	xor t2, a7, t2
	addi t2, t2, -1
	srli t2, t2, 63
	or t1, t1, t2
	addi t1, t1, -1
	and t1, t1, a4
	or s5, s5, t1
	addi t3, zero, 0
	sub t3, t3, t2
	and t1, a3, a4
	and t1, t1, t3
	or s6, s6, t1
	addi t2, t2, -1
	and a4, a4, t2
	addi a1, a1, 1
	addi a3, a3, 1
	addi a2, a2, -1
	bnez a2, 27b
	or s5, s5, a4
	addi a1, s0, 2047
	addi a1, a1, 513
	addi t5, zero, 1
	slli t5, t5, 11
	addi t0, zero, 0
28:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 28b
	addi a4, s0, 97
	addi a1, s0, 2047
	addi a1, a1, 513
	addi a5, s1, -97
29:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 29b
	addi s8, s6, 1
	addi s9, zero, 1
	addi s10, zero, 10
210:
	addi a1, s0, 2047
	addi a1, a1, 513
	add a2, a1, s9
	addi a3, zero, 1
	and a3, s8, a3
	addi a4, zero, 0
	sub a3, a4, a3
	addi a5, s1, 0
211:
	lbu t1, 0(a1)
	lbu t2, 0(a2)
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	sb t1, 0(a1)
	addi a1, a1, 1
	addi a2, a2, 1
	addi a5, a5, -1
	bnez a5, 211b
	srli s8, s8, 1
	add s9, s9, s9
	addi s10, s10, -1
	bnez s10, 210b
	addi a1, zero, 1
	xor a1, s4, a1
	addi a1, a1, -1
	srli a1, a1, 63
	addi a2, zero, 0
	sub a2, a2, s5
	or a2, a2, s5
	srli a2, a2, 63
	addi a3, zero, 1
	xor a2, a2, a3
	and a1, a1, a2
	addi s7, zero, 0
	sub s7, s7, a1
	addi a4, s0, 2047
	addi a4, a4, 513
	addi a5, s2, 0
	addi a6, s1, 0
212:
	lbu t1, 0(a4)
	and t1, t1, s7
	sb t1, 0(a5)
	addi a4, a4, 1
	addi a5, a5, 1
	addi a6, a6, -1
	bnez a6, 212b
	addi a1, s1, -98
	sub a1, a1, s6
	and a1, a1, s7
	sd a1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
	addi a1, zero, 1
	and a1, s7, a1
	or a0, a0, a1
	j 21f
20:
	addi a1, s2, 0
	addi t5, s1, 0
	addi t0, zero, 0
213:
	sb t0, 0(a1)
	addi a1, a1, 1
	addi t5, t5, -1
	bnez t5, 213b
	addi t1, zero, 0
	sd t1, 0(s3)
	addi a1, zero, 2
	xor a0, s4, a1
	addi a0, a0, -1
	srli a0, a0, 63
	add a0, a0, a0
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

vg_rsa_oaep_sha384_mgf1_encrypt_precomputed:
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
	addi a0, zero, 98
	sub a0, s1, a0
	srli a0, a0, 63
	bnez a0, 20f
	addi a0, zero, 98
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
	addi a5, zero, 48
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
	call {vg_sha384_init}
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	call {vg_sha512_update}
	addi a0, s0, 1024
	addi a1, s7, 0
	addi a2, s0, 1280
	call {vg_sha384_finalize}
	addi a4, s0, 1280
	addi a1, s0, 49
	addi a5, zero, 48
29:
	lbu t0, 0(a4)
	sb t0, 0(a1)
	addi a4, a4, 1
	addi a1, a1, 1
	addi a5, a5, -1
	bnez a5, 29b
	addi s6, s0, 1
	addi s7, zero, 48
	addi s8, s0, 49
	addi s9, s1, -49
	addi s10, zero, 0
	addi s11, zero, 0
210:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
	sub t1, s11, s9
	srli t1, t1, 63
	bnez t1, 210b
	addi s6, s0, 49
	addi s7, s1, -49
	addi s8, s0, 1
	addi s9, zero, 48
	addi s10, zero, 0
	addi s11, zero, 0
212:
	addi a0, s0, 1024
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 0(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, zero, 0
	addi a2, s6, 0
	addi a3, s7, 0
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 8(t1)
	jalr ra, 0(t1)
	addi a0, s0, 1024
	addi a1, s7, 4
	addi a2, s0, 1280
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 16(t1)
	jalr ra, 0(t1)
	addi a6, sp, 184
	ld a6, 0(a6)
	ld a6, 32(a6)
	addi a4, s0, 1280
	add a5, s8, s11
	sub t1, s9, s11
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
	addi t1, sp, 184
	ld t1, 0(t1)
	ld t1, 32(t1)
	addi s10, s10, 1
	add s11, s11, t1
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
