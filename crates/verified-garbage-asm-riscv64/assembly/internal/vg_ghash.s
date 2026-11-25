// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -16
	addi t0, sp, 0
	sd s0, 1952(t0)
	sd s1, 1960(t0)
	sd s2, 1968(t0)
	sd s3, 1976(t0)
	sd s4, 1984(t0)
	sd s5, 1992(t0)
	sd s6, 2000(t0)
	sd s7, 2008(t0)
	sd s8, 2016(t0)
	sd s9, 2024(t0)
	sd s10, 2032(t0)
	sd s11, 2040(t0)
	addi s9, sp, 1664
	lbu t1, 0(a0)
	slli t1, t1, 8
	lbu t0, 1(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 2(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 3(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 4(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 5(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 6(a0)
	or t1, t1, t0
	slli t1, t1, 8
	lbu t0, 7(a0)
	or t1, t1, t0
	lbu t2, 8(a0)
	slli t2, t2, 8
	lbu t0, 9(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 10(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 11(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 12(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 13(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 14(a0)
	or t2, t2, t0
	slli t2, t2, 8
	lbu t0, 15(a0)
	or t2, t2, t0
	lui s0, 69905
	addiw s0, s0, 273
	slli s0, s0, 32
	lui t0, 69905
	addiw t0, t0, 273
	add s0, s0, t0
	slli s1, s0, 1
	slli s2, s0, 2
	slli s3, s0, 3
	srli t5, t1, 63
	srli t6, t2, 63
	slli t4, t1, 1
	xor t4, t4, t6
	slli t2, t2, 1
	xor t2, t2, t5
	slli t6, t5, 63
	xor t4, t4, t6
	slli t6, t5, 62
	xor t4, t4, t6
	slli t6, t5, 57
	xor t4, t4, t6
	xor t3, t4, t2
	slli t5, t4, 32
	srli t5, t5, 32
	srli t6, t4, 32
	xor t0, t5, t6
	and a7, t5, s0
	sd a7, 0(s9)
	and a7, t5, s1
	sd a7, 8(s9)
	and a7, t5, s2
	sd a7, 16(s9)
	and a7, t5, s3
	sd a7, 24(s9)
	and a7, t6, s0
	sd a7, 32(s9)
	and a7, t6, s1
	sd a7, 40(s9)
	and a7, t6, s2
	sd a7, 48(s9)
	and a7, t6, s3
	sd a7, 56(s9)
	and a7, t0, s0
	sd a7, 64(s9)
	and a7, t0, s1
	sd a7, 72(s9)
	and a7, t0, s2
	sd a7, 80(s9)
	and a7, t0, s3
	sd a7, 88(s9)
	slli t5, t2, 32
	srli t5, t5, 32
	srli t6, t2, 32
	xor t0, t5, t6
	and a7, t5, s0
	sd a7, 96(s9)
	and a7, t5, s1
	sd a7, 104(s9)
	and a7, t5, s2
	sd a7, 112(s9)
	and a7, t5, s3
	sd a7, 120(s9)
	and a7, t6, s0
	sd a7, 128(s9)
	and a7, t6, s1
	sd a7, 136(s9)
	and a7, t6, s2
	sd a7, 144(s9)
	and a7, t6, s3
	sd a7, 152(s9)
	and a7, t0, s0
	sd a7, 160(s9)
	and a7, t0, s1
	sd a7, 168(s9)
	and a7, t0, s2
	sd a7, 176(s9)
	and a7, t0, s3
	sd a7, 184(s9)
	slli t5, t3, 32
	srli t5, t5, 32
	srli t6, t3, 32
	xor t0, t5, t6
	and a7, t5, s0
	sd a7, 192(s9)
	and a7, t5, s1
	sd a7, 200(s9)
	and a7, t5, s2
	sd a7, 208(s9)
	and a7, t5, s3
	sd a7, 216(s9)
	and a7, t6, s0
	sd a7, 224(s9)
	and a7, t6, s1
	sd a7, 232(s9)
	and a7, t6, s2
	sd a7, 240(s9)
	and a7, t6, s3
	sd a7, 248(s9)
	and a7, t0, s0
	sd a7, 256(s9)
	and a7, t0, s1
	sd a7, 264(s9)
	and a7, t0, s2
	sd a7, 272(s9)
	and a7, t0, s3
	sd a7, 280(s9)
	addi a0, s9, 0
	lbu s4, 0(a1)
	slli s4, s4, 8
	lbu t0, 1(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 2(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 3(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 4(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 5(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 6(a1)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 7(a1)
	or s4, s4, t0
	lbu s5, 8(a1)
	slli s5, s5, 8
	lbu t0, 9(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 10(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 11(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 12(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 13(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 14(a1)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 15(a1)
	or s5, s5, t0
	beqz a3, 20f
22:
	lbu s6, 0(a2)
	slli s6, s6, 8
	lbu t0, 1(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 2(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 3(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 4(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 5(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 6(a2)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 7(a2)
	or s6, s6, t0
	lbu s7, 8(a2)
	slli s7, s7, 8
	lbu t0, 9(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 10(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 11(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 12(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 13(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 14(a2)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 15(a2)
	or s7, s7, t0
	xor s4, s4, s6
	xor s5, s5, s7
	xor s9, s4, s5
	slli s10, s9, 32
	srli s10, s10, 32
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 192(a0)
	ld t5, 200(a0)
	ld t6, 208(a0)
	ld a5, 216(a0)
	addi s6, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s6, s6, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s6, s6, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s6, s6, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s6, s6, a6
	srli s11, s9, 32
	and t0, s11, s0
	and t1, s11, s1
	and t2, s11, s2
	and t3, s11, s3
	ld t4, 224(a0)
	ld t5, 232(a0)
	ld t6, 240(a0)
	ld a5, 248(a0)
	addi s7, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s7, s7, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s7, s7, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s7, s7, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s7, s7, a6
	xor s10, s10, s11
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 256(a0)
	ld t5, 264(a0)
	ld t6, 272(a0)
	ld a5, 280(a0)
	addi s8, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s8, s8, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s8, s8, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s8, s8, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s8, s8, a6
	xor s8, s8, s6
	xor s8, s8, s7
	slli s10, s8, 32
	xor s6, s6, s10
	srli s10, s8, 32
	xor s7, s7, s10
	addi a4, s6, 0
	addi s9, s7, 0
	slli s10, s4, 32
	srli s10, s10, 32
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 0(a0)
	ld t5, 8(a0)
	ld t6, 16(a0)
	ld a5, 24(a0)
	addi s6, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s6, s6, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s6, s6, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s6, s6, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s6, s6, a6
	srli s11, s4, 32
	and t0, s11, s0
	and t1, s11, s1
	and t2, s11, s2
	and t3, s11, s3
	ld t4, 32(a0)
	ld t5, 40(a0)
	ld t6, 48(a0)
	ld a5, 56(a0)
	addi s7, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s7, s7, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s7, s7, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s7, s7, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s7, s7, a6
	xor s10, s10, s11
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 64(a0)
	ld t5, 72(a0)
	ld t6, 80(a0)
	ld a5, 88(a0)
	addi s8, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s8, s8, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s8, s8, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s8, s8, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s8, s8, a6
	xor s8, s8, s6
	xor s8, s8, s7
	slli s10, s8, 32
	xor s6, s6, s10
	srli s10, s8, 32
	xor s7, s7, s10
	xor a4, a4, s6
	xor s9, s9, s7
	xor s9, s9, s6
	addi s4, s7, 0
	slli s10, s5, 32
	srli s10, s10, 32
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 96(a0)
	ld t5, 104(a0)
	ld t6, 112(a0)
	ld a5, 120(a0)
	addi s6, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s6, s6, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s6, s6, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s6, s6, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s6, s6, a6
	srli s11, s5, 32
	and t0, s11, s0
	and t1, s11, s1
	and t2, s11, s2
	and t3, s11, s3
	ld t4, 128(a0)
	ld t5, 136(a0)
	ld t6, 144(a0)
	ld a5, 152(a0)
	addi s7, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s7, s7, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s7, s7, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s7, s7, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s7, s7, a6
	xor s10, s10, s11
	and t0, s10, s0
	and t1, s10, s1
	and t2, s10, s2
	and t3, s10, s3
	ld t4, 160(a0)
	ld t5, 168(a0)
	ld t6, 176(a0)
	ld a5, 184(a0)
	addi s8, zero, 0
	mul a6, t0, t4
	mul a7, t1, a5
	xor a6, a6, a7
	mul a7, t2, t6
	xor a6, a6, a7
	mul a7, t3, t5
	xor a6, a6, a7
	and a6, a6, s0
	xor s8, s8, a6
	mul a6, t0, t5
	mul a7, t1, t4
	xor a6, a6, a7
	mul a7, t2, a5
	xor a6, a6, a7
	mul a7, t3, t6
	xor a6, a6, a7
	and a6, a6, s1
	xor s8, s8, a6
	mul a6, t0, t6
	mul a7, t1, t5
	xor a6, a6, a7
	mul a7, t2, t4
	xor a6, a6, a7
	mul a7, t3, a5
	xor a6, a6, a7
	and a6, a6, s2
	xor s8, s8, a6
	mul a6, t0, a5
	mul a7, t1, t6
	xor a6, a6, a7
	mul a7, t2, t5
	xor a6, a6, a7
	mul a7, t3, t4
	xor a6, a6, a7
	and a6, a6, s3
	xor s8, s8, a6
	xor s8, s8, s6
	xor s8, s8, s7
	slli s10, s8, 32
	xor s6, s6, s10
	srli s10, s8, 32
	xor s7, s7, s10
	xor a4, a4, s6
	xor a4, a4, s7
	xor s9, s9, s7
	xor s9, s9, s6
	slli t0, s6, 63
	xor a4, a4, t0
	slli t0, s6, 62
	xor a4, a4, t0
	slli t0, s6, 57
	xor a4, a4, t0
	srli t0, s6, 1
	xor s9, s9, t0
	srli t0, s6, 2
	xor s9, s9, t0
	srli t0, s6, 7
	xor s9, s9, t0
	xor s4, s4, a4
	srli t0, a4, 1
	xor s4, s4, t0
	srli t0, a4, 2
	xor s4, s4, t0
	srli t0, a4, 7
	xor s4, s4, t0
	slli t0, a4, 63
	xor s9, s9, t0
	slli t0, a4, 62
	xor s9, s9, t0
	slli t0, a4, 57
	xor s9, s9, t0
	addi s5, s9, 0
	addi a2, a2, 16
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
21:
	addi t1, s4, 0
	addi t2, s5, 0
	addi t0, sp, 0
	ld s0, 1952(t0)
	ld s1, 1960(t0)
	ld s2, 1968(t0)
	ld s3, 1976(t0)
	ld s4, 1984(t0)
	ld s5, 1992(t0)
	ld s6, 2000(t0)
	ld s7, 2008(t0)
	ld s8, 2016(t0)
	ld s9, 2024(t0)
	ld s10, 2032(t0)
	ld s11, 2040(t0)
	addi sp, sp, 16
	addi sp, sp, 2032
	srli t3, t1, 56
	sb t3, 0(a1)
	srli t3, t1, 48
	sb t3, 1(a1)
	srli t3, t1, 40
	sb t3, 2(a1)
	srli t3, t1, 32
	sb t3, 3(a1)
	srli t3, t1, 24
	sb t3, 4(a1)
	srli t3, t1, 16
	sb t3, 5(a1)
	srli t3, t1, 8
	sb t3, 6(a1)
	srli t3, t1, 0
	sb t3, 7(a1)
	srli t3, t2, 56
	sb t3, 8(a1)
	srli t3, t2, 48
	sb t3, 9(a1)
	srli t3, t2, 40
	sb t3, 10(a1)
	srli t3, t2, 32
	sb t3, 11(a1)
	srli t3, t2, 24
	sb t3, 12(a1)
	srli t3, t2, 16
	sb t3, 13(a1)
	srli t3, t2, 8
	sb t3, 14(a1)
	srli t3, t2, 0
	sb t3, 15(a1)
	ret
	.option pop
