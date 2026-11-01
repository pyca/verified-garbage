// The functions of `src/x25519.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	lbu a4, 0(a2)
	lbu a5, 1(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 0(a3)
	sw a4, 96(a3)
	lbu a4, 4(a2)
	lbu a5, 5(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 4(a3)
	sw a4, 100(a3)
	lbu a4, 8(a2)
	lbu a5, 9(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 8(a3)
	sw a4, 104(a3)
	lbu a4, 12(a2)
	lbu a5, 13(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 12(a3)
	sw a4, 108(a3)
	lbu a4, 16(a2)
	lbu a5, 17(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 16(a3)
	sw a4, 112(a3)
	lbu a4, 20(a2)
	lbu a5, 21(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 20(a3)
	sw a4, 116(a3)
	lbu a4, 24(a2)
	lbu a5, 25(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(a2)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 24(a3)
	sw a4, 120(a3)
	lbu a4, 28(a2)
	lbu a5, 29(a2)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(a2)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(a2)
	slli a5, a5, 24
	or a4, a4, a5
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 28(a3)
	sw a4, 124(a3)
	addi a4, zero, 1
	addi a5, zero, 0
	lui a2, 30
	addiw a2, a2, -1215
	sw a4, 32(a3)
	sw a5, 64(a3)
	sw a4, 128(a3)
	sw a2, 448(a3)
	sw a5, 36(a3)
	sw a5, 40(a3)
	sw a5, 44(a3)
	sw a5, 48(a3)
	sw a5, 52(a3)
	sw a5, 56(a3)
	sw a5, 60(a3)
	sw a5, 68(a3)
	sw a5, 72(a3)
	sw a5, 76(a3)
	sw a5, 80(a3)
	sw a5, 84(a3)
	sw a5, 88(a3)
	sw a5, 92(a3)
	sw a5, 132(a3)
	sw a5, 136(a3)
	sw a5, 140(a3)
	sw a5, 144(a3)
	sw a5, 148(a3)
	sw a5, 152(a3)
	sw a5, 156(a3)
	sw a5, 452(a3)
	sw a5, 456(a3)
	sw a5, 460(a3)
	sw a5, 464(a3)
	sw a5, 468(a3)
	sw a5, 472(a3)
	sw a5, 476(a3)
	addi a6, a3, 0
	addi t0, zero, 32
20:
	lbu a4, 0(a1)
	slli a5, a4, 63
	srli a5, a5, 63
	sb a5, 608(a6)
	slli a5, a4, 62
	srli a5, a5, 63
	sb a5, 609(a6)
	slli a5, a4, 61
	srli a5, a5, 63
	sb a5, 610(a6)
	slli a5, a4, 60
	srli a5, a5, 63
	sb a5, 611(a6)
	slli a5, a4, 59
	srli a5, a5, 63
	sb a5, 612(a6)
	slli a5, a4, 58
	srli a5, a5, 63
	sb a5, 613(a6)
	slli a5, a4, 57
	srli a5, a5, 63
	sb a5, 614(a6)
	slli a5, a4, 56
	srli a5, a5, 63
	sb a5, 615(a6)
	addi a1, a1, 1
	addi a6, a6, 8
	addi t0, t0, -1
	bnez t0, 20b
	addi a4, zero, 0
	sb a4, 608(a3)
	sb a4, 609(a3)
	sb a4, 610(a3)
	addi a4, zero, 1
	sb a4, 862(a3)
	addi t1, zero, 255
	addi t2, zero, 0
21:
	addi t1, t1, -1
	add a1, a3, t1
	lbu a1, 608(a1)
	xor t2, t2, a1
	addi t0, zero, 0
	sub t0, t0, t2
	ld a2, 32(a3)
	ld a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 32(a3)
	sd a4, 96(a3)
	ld a2, 40(a3)
	ld a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 40(a3)
	sd a4, 104(a3)
	ld a2, 48(a3)
	ld a4, 112(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 48(a3)
	sd a4, 112(a3)
	ld a2, 56(a3)
	ld a4, 120(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 56(a3)
	sd a4, 120(a3)
	ld a2, 64(a3)
	ld a4, 128(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 64(a3)
	sd a4, 128(a3)
	ld a2, 72(a3)
	ld a4, 136(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 72(a3)
	sd a4, 136(a3)
	ld a2, 80(a3)
	ld a4, 144(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 80(a3)
	sd a4, 144(a3)
	ld a2, 88(a3)
	ld a4, 152(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 88(a3)
	sd a4, 152(a3)
	addi t2, a1, 0
	ld t3, 32(a3)
	ld a7, 64(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 40(a3)
	ld a7, 72(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 48(a3)
	ld a7, 80(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 56(a3)
	ld a7, 88(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 160(a3)
	sd t4, 168(a3)
	sd t5, 176(a3)
	sd t6, 184(a3)
	ld t3, 160(a3)
	ld t4, 168(a3)
	ld t5, 176(a3)
	ld t6, 184(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 544(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 544(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 160(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 544(a3)
	srli a7, a5, 63
	ld a5, 552(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 552(a3)
	srli a7, a5, 63
	ld a5, 560(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 168(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 560(a3)
	srli a7, a5, 63
	ld a5, 568(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 568(a3)
	srli a7, a5, 63
	ld a5, 576(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 176(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 576(a3)
	srli a7, a5, 63
	ld a5, 584(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 584(a3)
	srli a7, a5, 63
	ld a5, 592(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 184(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 592(a3)
	srli a7, a5, 63
	ld a5, 600(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 600(a3)
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 288(a3)
	sd t4, 296(a3)
	sd t5, 304(a3)
	sd t6, 312(a3)
	ld t3, 32(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 40(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 48(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 56(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 192(a3)
	sd t4, 200(a3)
	sd t5, 208(a3)
	sd t6, 216(a3)
	ld t3, 192(a3)
	ld t4, 200(a3)
	ld t5, 208(a3)
	ld t6, 216(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 544(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 544(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 192(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 544(a3)
	srli a7, a5, 63
	ld a5, 552(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 552(a3)
	srli a7, a5, 63
	ld a5, 560(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 200(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 560(a3)
	srli a7, a5, 63
	ld a5, 568(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 568(a3)
	srli a7, a5, 63
	ld a5, 576(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 208(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 576(a3)
	srli a7, a5, 63
	ld a5, 584(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 584(a3)
	srli a7, a5, 63
	ld a5, 592(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 216(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 592(a3)
	srli a7, a5, 63
	ld a5, 600(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 600(a3)
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 320(a3)
	sd t4, 328(a3)
	sd t5, 336(a3)
	sd t6, 344(a3)
	ld t3, 288(a3)
	ld a7, 320(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 296(a3)
	ld a7, 328(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 304(a3)
	ld a7, 336(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 312(a3)
	ld a7, 344(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 96(a3)
	ld a7, 128(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 104(a3)
	ld a7, 136(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 144(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 152(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 224(a3)
	sd t4, 232(a3)
	sd t5, 240(a3)
	sd t6, 248(a3)
	ld t3, 96(a3)
	ld a7, 128(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 104(a3)
	ld a7, 136(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 144(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 152(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 256(a3)
	sd t4, 264(a3)
	sd t5, 272(a3)
	sd t6, 280(a3)
	ld t3, 160(a3)
	ld t4, 168(a3)
	ld t5, 176(a3)
	ld t6, 184(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 256(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 264(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 256(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 272(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 264(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 256(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 280(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 272(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 264(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 256(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 280(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 272(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 264(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 280(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 272(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 280(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 192(a3)
	ld t4, 200(a3)
	ld t5, 208(a3)
	ld t6, 216(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 224(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 232(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 224(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 240(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 232(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 224(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 248(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 240(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 232(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 224(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 248(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 240(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 232(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 248(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 240(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 248(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 416(a3)
	sd t4, 424(a3)
	sd t5, 432(a3)
	sd t6, 440(a3)
	ld t3, 384(a3)
	ld a7, 416(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 392(a3)
	ld a7, 424(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 400(a3)
	ld a7, 432(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 408(a3)
	ld a7, 440(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 96(a3)
	sd t4, 104(a3)
	sd t5, 112(a3)
	sd t6, 120(a3)
	ld t3, 96(a3)
	ld t4, 104(a3)
	ld t5, 112(a3)
	ld t6, 120(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 544(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 544(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 96(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 544(a3)
	srli a7, a5, 63
	ld a5, 552(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 552(a3)
	srli a7, a5, 63
	ld a5, 560(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 104(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 560(a3)
	srli a7, a5, 63
	ld a5, 568(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 568(a3)
	srli a7, a5, 63
	ld a5, 576(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 112(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 576(a3)
	srli a7, a5, 63
	ld a5, 584(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 584(a3)
	srli a7, a5, 63
	ld a5, 592(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 120(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 592(a3)
	srli a7, a5, 63
	ld a5, 600(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 600(a3)
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 96(a3)
	sd t4, 104(a3)
	sd t5, 112(a3)
	sd t6, 120(a3)
	ld t3, 384(a3)
	ld a7, 416(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 392(a3)
	ld a7, 424(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 400(a3)
	ld a7, 432(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 408(a3)
	ld a7, 440(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 128(a3)
	sd t4, 136(a3)
	sd t5, 144(a3)
	sd t6, 152(a3)
	ld t3, 128(a3)
	ld t4, 136(a3)
	ld t5, 144(a3)
	ld t6, 152(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 544(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 544(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 128(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 544(a3)
	srli a7, a5, 63
	ld a5, 552(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 552(a3)
	srli a7, a5, 63
	ld a5, 560(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 136(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 560(a3)
	srli a7, a5, 63
	ld a5, 568(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 568(a3)
	srli a7, a5, 63
	ld a5, 576(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 144(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 576(a3)
	srli a7, a5, 63
	ld a5, 584(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 584(a3)
	srli a7, a5, 63
	ld a5, 592(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 152(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 592(a3)
	srli a7, a5, 63
	ld a5, 600(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 600(a3)
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 128(a3)
	sd t4, 136(a3)
	sd t5, 144(a3)
	sd t6, 152(a3)
	ld t3, 128(a3)
	ld t4, 136(a3)
	ld t5, 144(a3)
	ld t6, 152(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 0(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 8(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 0(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 16(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 8(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 0(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 24(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 16(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 8(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 0(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 24(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 16(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 8(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 24(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 16(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 24(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 128(a3)
	sd t4, 136(a3)
	sd t5, 144(a3)
	sd t6, 152(a3)
	ld t3, 320(a3)
	ld t4, 328(a3)
	ld t5, 336(a3)
	ld t6, 344(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 288(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 296(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 288(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 304(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 296(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 288(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 312(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 304(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 296(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 288(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 312(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 304(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 296(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 312(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 304(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 312(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 32(a3)
	sd t4, 40(a3)
	sd t5, 48(a3)
	sd t6, 56(a3)
	ld t3, 352(a3)
	ld t4, 360(a3)
	ld t5, 368(a3)
	ld t6, 376(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 448(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 456(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 448(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 464(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 456(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 448(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 464(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 456(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 448(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 464(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 456(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 464(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	ld t3, 288(a3)
	ld a7, 64(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 296(a3)
	ld a7, 72(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 304(a3)
	ld a7, 80(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 312(a3)
	ld a7, 88(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	ld t3, 64(a3)
	ld t4, 72(a3)
	ld t5, 80(a3)
	ld t6, 88(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 352(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 360(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 352(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 368(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 360(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 352(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 368(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 360(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 352(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 368(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 360(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 368(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	bnez t1, 21b
	addi t0, zero, 0
	sub t0, t0, t2
	ld a2, 32(a3)
	ld a4, 96(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 32(a3)
	sd a4, 96(a3)
	ld a2, 40(a3)
	ld a4, 104(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 40(a3)
	sd a4, 104(a3)
	ld a2, 48(a3)
	ld a4, 112(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 48(a3)
	sd a4, 112(a3)
	ld a2, 56(a3)
	ld a4, 120(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 56(a3)
	sd a4, 120(a3)
	ld a2, 64(a3)
	ld a4, 128(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 64(a3)
	sd a4, 128(a3)
	ld a2, 72(a3)
	ld a4, 136(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 72(a3)
	sd a4, 136(a3)
	ld a2, 80(a3)
	ld a4, 144(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 80(a3)
	sd a4, 144(a3)
	ld a2, 88(a3)
	ld a4, 152(a3)
	xor a5, a2, a4
	and a5, a5, t0
	xor a2, a2, a5
	xor a4, a4, a5
	sd a2, 88(a3)
	sd a4, 152(a3)
	addi a1, zero, 1
	addi a2, zero, 0
	sw a1, 480(a3)
	sw a2, 484(a3)
	sw a2, 488(a3)
	sw a2, 492(a3)
	sw a2, 496(a3)
	sw a2, 500(a3)
	sw a2, 504(a3)
	sw a2, 508(a3)
	addi t1, zero, 255
22:
	addi t1, t1, -1
	ld t3, 480(a3)
	ld t4, 488(a3)
	ld t5, 496(a3)
	ld t6, 504(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	sd a4, 544(a3)
	addi a4, zero, 0
	mul a7, t3, t4
	mulhu t0, t3, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	mul a7, t3, t5
	mulhu t0, t3, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	mul a7, t3, t6
	mulhu t0, t3, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	mul a7, t4, t5
	mulhu t0, t4, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	mul a7, t4, t6
	mulhu t0, t4, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	mul a7, t5, t6
	mulhu t0, t5, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a5, zero, 0
	addi a4, zero, 0
	srli a7, a5, 63
	ld a5, 544(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 480(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 544(a3)
	srli a7, a5, 63
	ld a5, 552(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 552(a3)
	srli a7, a5, 63
	ld a5, 560(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 488(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 560(a3)
	srli a7, a5, 63
	ld a5, 568(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 568(a3)
	srli a7, a5, 63
	ld a5, 576(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 496(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 576(a3)
	srli a7, a5, 63
	ld a5, 584(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 584(a3)
	srli a7, a5, 63
	ld a5, 592(a3)
	slli a6, a5, 1
	or a6, a6, a7
	ld t3, 504(a3)
	mul t0, t3, t3
	mulhu t3, t3, t3
	add a6, a6, t0
	sltu a7, a6, t0
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 592(a3)
	srli a7, a5, 63
	ld a5, 600(a3)
	slli a6, a5, 1
	or a6, a6, a7
	add a6, a6, t3
	sltu a7, a6, t3
	add a6, a6, a4
	sltu t0, a6, a4
	add a4, a7, t0
	sd a6, 600(a3)
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 480(a3)
	sd t4, 488(a3)
	sd t5, 496(a3)
	sd t6, 504(a3)
	addi a2, t1, -4
	beqz a2, 23f
	addi a2, t1, -2
	beqz a2, 25f
	ld t3, 64(a3)
	ld t4, 72(a3)
	ld t5, 80(a3)
	ld t6, 88(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 480(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 488(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 480(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 496(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 488(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 480(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 496(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 488(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 480(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 496(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 488(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 496(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 480(a3)
	sd t4, 488(a3)
	sd t5, 496(a3)
	sd t6, 504(a3)
	j 26f
25:
26:
	j 24f
23:
24:
	bnez t1, 22b
	ld t3, 480(a3)
	ld t4, 488(a3)
	ld t5, 496(a3)
	ld t6, 504(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 32(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 544(a3)
	addi a4, zero, 0
	ld t0, 40(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 32(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 552(a3)
	addi a5, zero, 0
	ld t0, 48(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 40(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 32(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 560(a3)
	addi a6, zero, 0
	ld t0, 56(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 48(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 40(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 32(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 568(a3)
	addi a4, zero, 0
	ld t0, 56(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 48(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 40(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 576(a3)
	addi a5, zero, 0
	ld t0, 56(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 48(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 584(a3)
	addi a6, zero, 0
	ld t0, 56(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 592(a3)
	addi a4, zero, 0
	sd a5, 600(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 544(a3)
	ld a7, 576(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 552(a3)
	ld a7, 584(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 560(a3)
	ld a7, 592(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 568(a3)
	ld a7, 600(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 32(a3)
	sd t4, 40(a3)
	sd t5, 48(a3)
	sd t6, 56(a3)
	lwu a4, 60(a3)
	srli a5, a4, 31
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 60(a3)
	addi a2, zero, 19
	mul a5, a5, a2
	lwu a4, 32(a3)
	add a4, a4, a5
	sw a4, 32(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a5
	sw a4, 36(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a5
	sw a4, 40(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a5
	sw a4, 44(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a5
	sw a4, 48(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a5
	sw a4, 52(a3)
	srli a5, a4, 32
	lwu a4, 56(a3)
	add a4, a4, a5
	sw a4, 56(a3)
	srli a5, a4, 32
	lwu a4, 60(a3)
	add a4, a4, a5
	sw a4, 60(a3)
	srli a5, a4, 32
	addi a5, zero, 19
	lwu a4, 32(a3)
	add a4, a4, a5
	sw a4, 512(a3)
	srli a5, a4, 32
	lwu a4, 36(a3)
	add a4, a4, a5
	sw a4, 516(a3)
	srli a5, a4, 32
	lwu a4, 40(a3)
	add a4, a4, a5
	sw a4, 520(a3)
	srli a5, a4, 32
	lwu a4, 44(a3)
	add a4, a4, a5
	sw a4, 524(a3)
	srli a5, a4, 32
	lwu a4, 48(a3)
	add a4, a4, a5
	sw a4, 528(a3)
	srli a5, a4, 32
	lwu a4, 52(a3)
	add a4, a4, a5
	sw a4, 532(a3)
	srli a5, a4, 32
	lwu a4, 56(a3)
	add a4, a4, a5
	sw a4, 536(a3)
	srli a5, a4, 32
	lwu a4, 60(a3)
	add a4, a4, a5
	sw a4, 540(a3)
	srli a5, a4, 32
	lwu a4, 540(a3)
	srli t0, a4, 31
	addi a1, zero, 0
	sub t0, a1, t0
	slli a4, a4, 33
	srli a4, a4, 33
	sw a4, 540(a3)
	lwu a2, 32(a3)
	lwu a4, 512(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 0(a0)
	srli a4, a2, 8
	sb a4, 1(a0)
	srli a4, a2, 16
	sb a4, 2(a0)
	srli a4, a2, 24
	sb a4, 3(a0)
	lwu a2, 36(a3)
	lwu a4, 516(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 4(a0)
	srli a4, a2, 8
	sb a4, 5(a0)
	srli a4, a2, 16
	sb a4, 6(a0)
	srli a4, a2, 24
	sb a4, 7(a0)
	lwu a2, 40(a3)
	lwu a4, 520(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 8(a0)
	srli a4, a2, 8
	sb a4, 9(a0)
	srli a4, a2, 16
	sb a4, 10(a0)
	srli a4, a2, 24
	sb a4, 11(a0)
	lwu a2, 44(a3)
	lwu a4, 524(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 12(a0)
	srli a4, a2, 8
	sb a4, 13(a0)
	srli a4, a2, 16
	sb a4, 14(a0)
	srli a4, a2, 24
	sb a4, 15(a0)
	lwu a2, 48(a3)
	lwu a4, 528(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 16(a0)
	srli a4, a2, 8
	sb a4, 17(a0)
	srli a4, a2, 16
	sb a4, 18(a0)
	srli a4, a2, 24
	sb a4, 19(a0)
	lwu a2, 52(a3)
	lwu a4, 532(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 20(a0)
	srli a4, a2, 8
	sb a4, 21(a0)
	srli a4, a2, 16
	sb a4, 22(a0)
	srli a4, a2, 24
	sb a4, 23(a0)
	lwu a2, 56(a3)
	lwu a4, 536(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 24(a0)
	srli a4, a2, 8
	sb a4, 25(a0)
	srli a4, a2, 16
	sb a4, 26(a0)
	srli a4, a2, 24
	sb a4, 27(a0)
	lwu a2, 60(a3)
	lwu a4, 540(a3)
	xor a4, a4, a2
	and a4, a4, t0
	xor a2, a2, a4
	sb a2, 28(a0)
	srli a4, a2, 8
	sb a4, 29(a0)
	srli a4, a2, 16
	sb a4, 30(a0)
	srli a4, a2, 24
	sb a4, 31(a0)
	ret
	.option pop
