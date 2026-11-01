// The functions of `src/internal/vg_ed25519_scalar_reduce.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_reduce:
	.option push
	.option arch, +m, +c
	addi a3, a2, 0
	addi a3, a3, 7
	andi a3, a3, -8
	addi t3, a1, 0
	addi a4, zero, 0
	sw a4, 160(a3)
	sw a4, 164(a3)
	sw a4, 168(a3)
	sw a4, 172(a3)
	sw a4, 176(a3)
	sw a4, 180(a3)
	sw a4, 184(a3)
	sw a4, 188(a3)
	addi t4, zero, 64
20:
	addi t4, t4, -1
	add a4, t3, t4
	lbu t5, 0(a4)
	slli a5, t5, 56
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 57
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 58
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 59
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 60
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 61
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 62
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	slli a5, t5, 63
	srli a5, a5, 63
	lwu a4, 160(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 160(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 164(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 168(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 172(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 176(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 180(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 184(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	add a4, a4, a4
	add a4, a4, a5
	sw a4, 188(a3)
	srli a5, a4, 32
	addi a5, zero, 1
	lwu a4, 160(a3)
	lui a2, 667811
	addiw a2, a2, -1006
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 192(a3)
	srli a5, a4, 32
	lwu a4, 164(a3)
	lui a2, 687834
	addiw a2, a2, -795
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 196(a3)
	srli a5, a4, 32
	lwu a4, 168(a3)
	lui a2, 381062
	addiw a2, a2, 809
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 200(a3)
	srli a5, a4, 32
	lwu a4, 172(a3)
	lui a2, 963088
	addiw a2, a2, 1569
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 204(a3)
	srli a5, a4, 32
	lwu a4, 176(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 208(a3)
	srli a5, a4, 32
	lwu a4, 180(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 212(a3)
	srli a5, a4, 32
	lwu a4, 184(a3)
	lui a2, 0
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 216(a3)
	srli a5, a4, 32
	lwu a4, 188(a3)
	lui a2, 983040
	addiw a2, a2, -1
	slli a2, a2, 32
	srli a2, a2, 32
	add a4, a4, a2
	add a4, a4, a5
	sw a4, 220(a3)
	srli a5, a4, 32
	addi t0, zero, 0
	sub t0, t0, a5
	lwu a2, 160(a3)
	lwu a4, 192(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 160(a3)
	sw a4, 192(a3)
	lwu a2, 164(a3)
	lwu a4, 196(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 164(a3)
	sw a4, 196(a3)
	lwu a2, 168(a3)
	lwu a4, 200(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 168(a3)
	sw a4, 200(a3)
	lwu a2, 172(a3)
	lwu a4, 204(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 172(a3)
	sw a4, 204(a3)
	lwu a2, 176(a3)
	lwu a4, 208(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 176(a3)
	sw a4, 208(a3)
	lwu a2, 180(a3)
	lwu a4, 212(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 180(a3)
	sw a4, 212(a3)
	lwu a2, 184(a3)
	lwu a4, 216(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 184(a3)
	sw a4, 216(a3)
	lwu a2, 188(a3)
	lwu a4, 220(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sw a2, 188(a3)
	sw a4, 220(a3)
	bnez t4, 20b
	lwu a4, 160(a3)
	sb a4, 0(a0)
	srli a5, a4, 8
	sb a5, 1(a0)
	srli a5, a4, 16
	sb a5, 2(a0)
	srli a5, a4, 24
	sb a5, 3(a0)
	lwu a4, 164(a3)
	sb a4, 4(a0)
	srli a5, a4, 8
	sb a5, 5(a0)
	srli a5, a4, 16
	sb a5, 6(a0)
	srli a5, a4, 24
	sb a5, 7(a0)
	lwu a4, 168(a3)
	sb a4, 8(a0)
	srli a5, a4, 8
	sb a5, 9(a0)
	srli a5, a4, 16
	sb a5, 10(a0)
	srli a5, a4, 24
	sb a5, 11(a0)
	lwu a4, 172(a3)
	sb a4, 12(a0)
	srli a5, a4, 8
	sb a5, 13(a0)
	srli a5, a4, 16
	sb a5, 14(a0)
	srli a5, a4, 24
	sb a5, 15(a0)
	lwu a4, 176(a3)
	sb a4, 16(a0)
	srli a5, a4, 8
	sb a5, 17(a0)
	srli a5, a4, 16
	sb a5, 18(a0)
	srli a5, a4, 24
	sb a5, 19(a0)
	lwu a4, 180(a3)
	sb a4, 20(a0)
	srli a5, a4, 8
	sb a5, 21(a0)
	srli a5, a4, 16
	sb a5, 22(a0)
	srli a5, a4, 24
	sb a5, 23(a0)
	lwu a4, 184(a3)
	sb a4, 24(a0)
	srli a5, a4, 8
	sb a5, 25(a0)
	srli a5, a4, 16
	sb a5, 26(a0)
	srli a5, a4, 24
	sb a5, 27(a0)
	lwu a4, 188(a3)
	sb a4, 28(a0)
	srli a5, a4, 8
	sb a5, 29(a0)
	srli a5, a4, 16
	sb a5, 30(a0)
	srli a5, a4, 24
	sb a5, 31(a0)
	ret
	.option pop
