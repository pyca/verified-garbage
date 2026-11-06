// The functions of `src/sha3.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update:
	.option push
	.option arch, +m, +c
	addi a5, a4, 0
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 144
	addi t0, a5, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	sd s7, 560(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	addi s7, a5, 0
	beqz s6, 20f
22:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 23f
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 24f
23:
	beqz t4, 25f
	lbu t1, 0(s5)
	lbu t3, 1(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 2(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 3(s5)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 4(s5)
	lbu t3, 5(s5)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(s5)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(s5)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 26f
25:
	ld t1, 0(s5)
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
26:
24:
	sub t1, s4, s3
	beqz t1, 27f
	j 28f
27:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, s7, 0
	call {vg_keccak_f1600}
28:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, s7, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	ld s7, 560(t0)
	ret
	.option pop

vg_sha3_224_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi a3, sp, 0
	sd ra, 0(a3)
	sd s2, 8(a3)
	sd s3, 16(a3)
	sd s4, 24(a3)
	addi s2, a0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi a2, a1, 0
	addi a1, zero, 144
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a0, s2, 0
	addi a1, zero, 144
	addi a2, zero, 0
	addi a3, s3, 0
	addi a4, zero, 28
	call {vg_keccak_squeeze}
	ld ra, 0(s4)
	ld s2, 8(s4)
	ld s3, 16(s4)
	ld s4, 24(s4)
	addi sp, sp, 32
	ret
	.option pop

vg_sha3_256_update:
	.option push
	.option arch, +m, +c
	addi a5, a4, 0
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 136
	addi t0, a5, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	sd s7, 560(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	addi s7, a5, 0
	beqz s6, 20f
22:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 23f
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 24f
23:
	beqz t4, 25f
	lbu t1, 0(s5)
	lbu t3, 1(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 2(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 3(s5)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 4(s5)
	lbu t3, 5(s5)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(s5)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(s5)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 26f
25:
	ld t1, 0(s5)
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
26:
24:
	sub t1, s4, s3
	beqz t1, 27f
	j 28f
27:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, s7, 0
	call {vg_keccak_f1600}
28:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, s7, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	ld s7, 560(t0)
	ret
	.option pop

vg_sha3_256_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi a3, sp, 0
	sd ra, 0(a3)
	sd s2, 8(a3)
	sd s3, 16(a3)
	sd s4, 24(a3)
	addi s2, a0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi a2, a1, 0
	addi a1, zero, 136
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a0, s2, 0
	addi a1, zero, 136
	addi a2, zero, 0
	addi a3, s3, 0
	addi a4, zero, 32
	call {vg_keccak_squeeze}
	ld ra, 0(s4)
	ld s2, 8(s4)
	ld s3, 16(s4)
	ld s4, 24(s4)
	addi sp, sp, 32
	ret
	.option pop

vg_sha3_384_update:
	.option push
	.option arch, +m, +c
	addi a5, a4, 0
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 104
	addi t0, a5, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	sd s7, 560(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	addi s7, a5, 0
	beqz s6, 20f
22:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 23f
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 24f
23:
	beqz t4, 25f
	lbu t1, 0(s5)
	lbu t3, 1(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 2(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 3(s5)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 4(s5)
	lbu t3, 5(s5)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(s5)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(s5)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 26f
25:
	ld t1, 0(s5)
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
26:
24:
	sub t1, s4, s3
	beqz t1, 27f
	j 28f
27:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, s7, 0
	call {vg_keccak_f1600}
28:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, s7, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	ld s7, 560(t0)
	ret
	.option pop

vg_sha3_384_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi a3, sp, 0
	sd ra, 0(a3)
	sd s2, 8(a3)
	sd s3, 16(a3)
	sd s4, 24(a3)
	addi s2, a0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi a2, a1, 0
	addi a1, zero, 104
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a0, s2, 0
	addi a1, zero, 104
	addi a2, zero, 0
	addi a3, s3, 0
	addi a4, zero, 48
	call {vg_keccak_squeeze}
	ld ra, 0(s4)
	ld s2, 8(s4)
	ld s3, 16(s4)
	ld s4, 24(s4)
	addi sp, sp, 32
	ret
	.option pop

vg_sha3_512_update:
	.option push
	.option arch, +m, +c
	addi a5, a4, 0
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 72
	addi t0, a5, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	sd s7, 560(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	addi s7, a5, 0
	beqz s6, 20f
22:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 23f
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 24f
23:
	beqz t4, 25f
	lbu t1, 0(s5)
	lbu t3, 1(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 2(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 3(s5)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 4(s5)
	lbu t3, 5(s5)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(s5)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(s5)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 26f
25:
	ld t1, 0(s5)
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
26:
24:
	sub t1, s4, s3
	beqz t1, 27f
	j 28f
27:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, s7, 0
	call {vg_keccak_f1600}
28:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, s7, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	ld s7, 560(t0)
	ret
	.option pop

vg_sha3_512_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -32
	addi a3, sp, 0
	sd ra, 0(a3)
	sd s2, 8(a3)
	sd s3, 16(a3)
	sd s4, 24(a3)
	addi s2, a0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi a2, a1, 0
	addi a1, zero, 72
	addi a3, zero, 6
	call {vg_keccak_pad}
	addi a0, s2, 0
	addi a1, zero, 72
	addi a2, zero, 0
	addi a3, s3, 0
	addi a4, zero, 64
	call {vg_keccak_squeeze}
	ld ra, 0(s4)
	ld s2, 8(s4)
	ld s3, 16(s4)
	ld s4, 24(s4)
	addi sp, sp, 32
	ret
	.option pop

vg_shake128_update:
	.option push
	.option arch, +m, +c
	addi a5, a4, 0
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 168
	addi t0, a5, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	sd s7, 560(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	addi s7, a5, 0
	beqz s6, 20f
22:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 23f
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 24f
23:
	beqz t4, 25f
	lbu t1, 0(s5)
	lbu t3, 1(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 2(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 3(s5)
	slli t3, t3, 24
	or t1, t1, t3
	lbu t4, 4(s5)
	lbu t3, 5(s5)
	slli t3, t3, 8
	or t4, t4, t3
	lbu t3, 6(s5)
	slli t3, t3, 16
	or t4, t4, t3
	lbu t3, 7(s5)
	slli t3, t3, 24
	or t4, t4, t3
	slli t4, t4, 32
	or t1, t1, t4
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 26f
25:
	ld t1, 0(s5)
	ld t3, 0(t2)
	xor t1, t1, t3
	sd t1, 0(t2)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
26:
24:
	sub t1, s4, s3
	beqz t1, 27f
	j 28f
27:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, s7, 0
	call {vg_keccak_f1600}
28:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, s7, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	ld s7, 560(t0)
	ret
	.option pop

vg_shake128_finalize:
	.option push
	.option arch, +m, +c
	addi a2, a1, 0
	addi a1, zero, 168
	addi a3, zero, 31
	addi sp, sp, -528
	addi t0, sp, 0
	sd ra, 512(t0)
	add t1, a0, a2
	lbu t2, 0(t1)
	xor t2, t2, a3
	sb t2, 0(t1)
	add t1, a0, a1
	addi t1, t1, -1
	lbu t2, 0(t1)
	xori t2, t2, 128
	sb t2, 0(t1)
	addi a1, sp, 0
	call {vg_keccak_f1600}
	addi t0, sp, 0
	ld ra, 512(t0)
	addi sp, sp, 528
	ret
	.option pop

vg_shake128_squeeze:
	.option push
	.option arch, +m, +c
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 168
	addi sp, sp, -560
	addi t0, sp, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	beqz s6, 20f
22:
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 25f
	add t2, s2, s4
	lbu t1, 0(t2)
	sb t1, 0(s5)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 26f
25:
	beqz t4, 27f
	ld t1, 0(t2)
	sb t1, 0(s5)
	srli t3, t1, 8
	sb t3, 1(s5)
	srli t3, t1, 16
	sb t3, 2(s5)
	srli t3, t1, 24
	sb t3, 3(s5)
	srli t3, t1, 32
	sb t3, 4(s5)
	srli t4, t3, 8
	sb t4, 5(s5)
	srli t4, t3, 16
	sb t4, 6(s5)
	srli t4, t3, 24
	sb t4, 7(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 28f
27:
	ld t1, 0(t2)
	sd t1, 0(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
28:
26:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, sp, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	addi sp, sp, 560
	ret
	.option pop

// vg_shake256_update: the function `vg_sha3_256_update`

vg_shake256_finalize:
	.option push
	.option arch, +m, +c
	addi a2, a1, 0
	addi a1, zero, 136
	addi a3, zero, 31
	addi sp, sp, -528
	addi t0, sp, 0
	sd ra, 512(t0)
	add t1, a0, a2
	lbu t2, 0(t1)
	xor t2, t2, a3
	sb t2, 0(t1)
	add t1, a0, a1
	addi t1, t1, -1
	lbu t2, 0(t1)
	xori t2, t2, 128
	sb t2, 0(t1)
	addi a1, sp, 0
	call {vg_keccak_f1600}
	addi t0, sp, 0
	ld ra, 512(t0)
	addi sp, sp, 528
	ret
	.option pop

vg_shake256_squeeze:
	.option push
	.option arch, +m, +c
	addi a4, a3, 0
	addi a3, a2, 0
	addi a2, a1, 0
	addi a1, zero, 136
	addi sp, sp, -560
	addi t0, sp, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	beqz s6, 20f
22:
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 25f
	add t2, s2, s4
	lbu t1, 0(t2)
	sb t1, 0(s5)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 26f
25:
	beqz t4, 27f
	ld t1, 0(t2)
	sb t1, 0(s5)
	srli t3, t1, 8
	sb t3, 1(s5)
	srli t3, t1, 16
	sb t3, 2(s5)
	srli t3, t1, 24
	sb t3, 3(s5)
	srli t3, t1, 32
	sb t3, 4(s5)
	srli t4, t3, 8
	sb t4, 5(s5)
	srli t4, t3, 16
	sb t4, 6(s5)
	srli t4, t3, 24
	sb t4, 7(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 28f
27:
	ld t1, 0(t2)
	sd t1, 0(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
28:
26:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, sp, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	addi sp, sp, 560
	ret
	.option pop
