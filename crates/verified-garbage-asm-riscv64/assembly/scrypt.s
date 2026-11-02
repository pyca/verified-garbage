// The functions of `src/scrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s3, 8(t0)
	sd a0, 16(t0)
	sd a1, 24(t0)
	sd a4, 32(t0)
	sd a5, 40(t0)
	sd a6, 48(t0)
	sd a7, 56(t0)
	addi s3, t0, 0
	addi a4, zero, 1
	slli a6, a6, 7
	call {vg_pbkdf2_hmac_sha256}
	ld a0, 40(s3)
	sd a0, 64(s3)
	ld t0, 40(s3)
	ld t1, 56(s3)
	or t0, t0, t1
	ld t1, 88(s3)
	or t0, t0, t1
	andi t0, t0, 7
	beqz t0, 20f
22:
	ld a0, 64(s3)
	ld a1, 32(s3)
	ld a2, 56(s3)
	ld a3, 80(s3)
	ld a4, 88(s3)
	call {vg_scrypt_romix_bytes}
	ld a0, 64(s3)
	ld a1, 32(s3)
	slli a1, a1, 7
	add a0, a0, a1
	sd a0, 64(s3)
	ld t0, 40(s3)
	ld t1, 48(s3)
	slli t1, t1, 7
	add t0, t0, t1
	sub t0, t0, a0
	bnez t0, 22b
	j 21f
20:
23:
	ld a0, 64(s3)
	ld a1, 32(s3)
	ld a2, 56(s3)
	ld a3, 80(s3)
	ld a4, 88(s3)
	call {vg_scrypt_romix}
	ld a0, 64(s3)
	ld a1, 32(s3)
	slli a1, a1, 7
	add a0, a0, a1
	sd a0, 64(s3)
	ld t0, 40(s3)
	ld t1, 48(s3)
	slli t1, t1, 7
	add t0, t0, t1
	sub t0, t0, a0
	bnez t0, 23b
21:
	ld a0, 16(s3)
	ld a1, 24(s3)
	ld a2, 40(s3)
	ld a3, 48(s3)
	slli a3, a3, 7
	addi a4, zero, 1
	ld a5, 104(s3)
	ld a6, 112(s3)
	call {vg_pbkdf2_hmac_sha256}
	ld ra, 0(s3)
	ld s3, 8(s3)
	addi sp, sp, 80
	ret
	.option pop
