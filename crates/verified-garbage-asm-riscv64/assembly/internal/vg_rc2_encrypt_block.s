// The functions of `src/internal/vg_rc2_encrypt_block.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_encrypt_block:
	.option push
	.option arch, +m, +c
	andi t0, a0, 7
	beqz t0, 20f
	addi t3, a0, 0
	addi t4, a2, 0
	addi t5, zero, 128
22:
	lbu a7, 0(t3)
	sb a7, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 22b
	j 21f
20:
	addi a2, a0, 0
21:
	lbu t1, 0(a1)
	lbu a7, 1(a1)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 2(a1)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 3(a1)
	slli a7, a7, 24
	or t1, t1, a7
	lbu t2, 4(a1)
	lbu a7, 5(a1)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 6(a1)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 7(a1)
	slli a7, a7, 24
	or t2, t2, a7
	slli t2, t2, 32
	or t1, t1, t2
	slli a3, t1, 48
	srli a3, a3, 48
	slli a4, t1, 32
	srli a4, a4, 48
	slli a5, t1, 16
	srli a5, a5, 48
	srli a6, t1, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 0(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 2(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 4(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 6(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 8(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 10(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 12(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 14(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 16(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 18(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 20(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 22(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 24(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 26(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 28(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 30(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 32(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 34(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 36(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 38(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 40(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 42(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 44(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 46(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 48(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 50(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 52(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 54(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 56(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 58(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 60(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 62(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 64(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 66(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 68(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 70(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 72(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 74(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 76(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 78(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 80(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 82(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 84(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 86(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 88(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 90(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 92(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 94(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 96(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 98(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 100(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 102(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 104(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 106(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 108(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 110(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 112(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 114(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 116(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 118(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 120(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 122(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 124(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 126(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t1, a4, 16
	or t1, t1, a3
	slli t2, a5, 32
	or t1, t1, t2
	slli t2, a6, 48
	or t1, t1, t2
	sb t1, 0(a1)
	srli a7, t1, 8
	sb a7, 1(a1)
	srli a7, t1, 16
	sb a7, 2(a1)
	srli a7, t1, 24
	sb a7, 3(a1)
	srli t2, t1, 32
	sb t2, 4(a1)
	srli a7, t2, 8
	sb a7, 5(a1)
	srli a7, t2, 16
	sb a7, 6(a1)
	srli a7, t2, 24
	sb a7, 7(a1)
	ret
	.option pop
