// The functions of `src/camellia.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1168
	addi a3, sp, 0
	addi a5, a3, 0
	addi a3, a1, 0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	sd s8, 704(a5)
	sd s9, 712(a5)
	sd s10, 720(a5)
	sd s11, 728(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 384(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 392(a5)
	lui t0, 4096
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 400(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 408(a5)
	lui t0, 0
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 464(a5)
	addi a1, a5, 1024
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 1048560
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 4096
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 0
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 1044496
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 4096
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 1044480
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 1048560
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 1044480
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 1048560
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lui t0, 4096
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 0
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 1044480
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 4096
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 4080
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lui t0, 1044496
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 1044496
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 0
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 1048560
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 4096
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 4080
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 4080
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 0(a1)
	lui t0, 4080
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 8(a1)
	lui t0, 1044480
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 16(a1)
	lui t0, 1044480
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 24(a1)
	lui t0, 1044480
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 32(a1)
	lui t0, 1044480
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 40(a1)
	lui t0, 0
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 48(a1)
	lui t0, 0
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 56(a1)
	addi a1, a1, 64
	lbu t0, 0(a0)
	sb t0, 768(a5)
	lbu t0, 1(a0)
	sb t0, 769(a5)
	lbu t0, 2(a0)
	sb t0, 770(a5)
	lbu t0, 3(a0)
	sb t0, 771(a5)
	lbu t0, 4(a0)
	sb t0, 772(a5)
	lbu t0, 5(a0)
	sb t0, 773(a5)
	lbu t0, 6(a0)
	sb t0, 774(a5)
	lbu t0, 7(a0)
	sb t0, 775(a5)
	lbu t0, 8(a0)
	sb t0, 776(a5)
	lbu t0, 9(a0)
	sb t0, 777(a5)
	lbu t0, 10(a0)
	sb t0, 778(a5)
	lbu t0, 11(a0)
	sb t0, 779(a5)
	lbu t0, 12(a0)
	sb t0, 780(a5)
	lbu t0, 13(a0)
	sb t0, 781(a5)
	lbu t0, 14(a0)
	sb t0, 782(a5)
	lbu t0, 15(a0)
	sb t0, 783(a5)
	addi t1, a3, -16
	beqz t1, 20f
	lbu t0, 16(a0)
	sb t0, 784(a5)
	lbu t0, 17(a0)
	sb t0, 785(a5)
	lbu t0, 18(a0)
	sb t0, 786(a5)
	lbu t0, 19(a0)
	sb t0, 787(a5)
	lbu t0, 20(a0)
	sb t0, 788(a5)
	lbu t0, 21(a0)
	sb t0, 789(a5)
	lbu t0, 22(a0)
	sb t0, 790(a5)
	lbu t0, 23(a0)
	sb t0, 791(a5)
	addi t1, a3, -24
	beqz t1, 22f
	lbu t0, 24(a0)
	sb t0, 792(a5)
	lbu t0, 25(a0)
	sb t0, 793(a5)
	lbu t0, 26(a0)
	sb t0, 794(a5)
	lbu t0, 27(a0)
	sb t0, 795(a5)
	lbu t0, 28(a0)
	sb t0, 796(a5)
	lbu t0, 29(a0)
	sb t0, 797(a5)
	lbu t0, 30(a0)
	sb t0, 798(a5)
	lbu t0, 31(a0)
	sb t0, 799(a5)
	j 23f
22:
	ld t0, 784(a5)
	xori t0, t0, -1
	sd t0, 792(a5)
23:
	j 21f
20:
	addi t0, zero, 0
	sd t0, 784(a5)
	sd t0, 792(a5)
21:
	addi a1, a5, 1024
	ld t0, 768(a5)
	sd t0, 800(a5)
	ld t0, 776(a5)
	sd t0, 808(a5)
	ld t0, 784(a5)
	ld t1, 800(a5)
	xor t0, t0, t1
	sd t0, 800(a5)
	ld t0, 792(a5)
	ld t1, 808(a5)
	xor t0, t0, t1
	sd t0, 808(a5)
	addi a4, zero, 3
	addi a0, a5, 800
24:
	ld s0, 8(a0)
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 0(a0)
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	sd s0, 576(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	sd s1, 584(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	sd s2, 592(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	sd s3, 600(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	sd s4, 608(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	sd s5, 616(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	sd s6, 624(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	sd s7, 632(a5)
	ld t0, 64(a1)
	xor s0, s0, t0
	ld t0, 72(a1)
	xor s1, s1, t0
	ld t0, 80(a1)
	xor s2, s2, t0
	ld t0, 88(a1)
	xor s3, s3, t0
	ld t0, 96(a1)
	xor s4, s4, t0
	ld t0, 104(a1)
	xor s5, s5, t0
	ld t0, 112(a1)
	xor s6, s6, t0
	ld t0, 120(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	sd s0, 512(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	sd s1, 520(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	sd s2, 528(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	sd s3, 536(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	sd s4, 544(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	sd s5, 552(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	sd s6, 560(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	sd s7, 568(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 800(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 808(a5)
	addi a1, a1, 128
	srli t1, a4, 1
	bnez t1, 25f
	ld t0, 800(a5)
	sd t0, 832(a5)
	ld t0, 808(a5)
	sd t0, 840(a5)
	j 26f
25:
	addi t1, a4, -3
	beqz t1, 27f
	ld t0, 800(a5)
	sd t0, 816(a5)
	ld t0, 808(a5)
	sd t0, 824(a5)
	ld t0, 784(a5)
	ld t1, 800(a5)
	xor t0, t0, t1
	sd t0, 800(a5)
	ld t0, 792(a5)
	ld t1, 808(a5)
	xor t0, t0, t1
	sd t0, 808(a5)
	j 28f
27:
	ld t0, 768(a5)
	ld t1, 800(a5)
	xor t0, t0, t1
	sd t0, 800(a5)
	ld t0, 776(a5)
	ld t1, 808(a5)
	xor t0, t0, t1
	sd t0, 808(a5)
28:
26:
	addi a4, a4, -1
	bnez a4, 24b
	lbu s0, 768(a5)
	slli s0, s0, 8
	lbu t0, 769(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 770(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 771(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 772(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 773(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 774(a5)
	or s0, s0, t0
	slli s0, s0, 8
	lbu t0, 775(a5)
	or s0, s0, t0
	lbu s1, 776(a5)
	slli s1, s1, 8
	lbu t0, 777(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 778(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 779(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 780(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 781(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 782(a5)
	or s1, s1, t0
	slli s1, s1, 8
	lbu t0, 783(a5)
	or s1, s1, t0
	lbu s2, 784(a5)
	slli s2, s2, 8
	lbu t0, 785(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 786(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 787(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 788(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 789(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 790(a5)
	or s2, s2, t0
	slli s2, s2, 8
	lbu t0, 791(a5)
	or s2, s2, t0
	lbu s3, 792(a5)
	slli s3, s3, 8
	lbu t0, 793(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 794(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 795(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 796(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 797(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 798(a5)
	or s3, s3, t0
	slli s3, s3, 8
	lbu t0, 799(a5)
	or s3, s3, t0
	lbu s4, 816(a5)
	slli s4, s4, 8
	lbu t0, 817(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 818(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 819(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 820(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 821(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 822(a5)
	or s4, s4, t0
	slli s4, s4, 8
	lbu t0, 823(a5)
	or s4, s4, t0
	lbu s5, 824(a5)
	slli s5, s5, 8
	lbu t0, 825(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 826(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 827(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 828(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 829(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 830(a5)
	or s5, s5, t0
	slli s5, s5, 8
	lbu t0, 831(a5)
	or s5, s5, t0
	lbu s6, 832(a5)
	slli s6, s6, 8
	lbu t0, 833(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 834(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 835(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 836(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 837(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 838(a5)
	or s6, s6, t0
	slli s6, s6, 8
	lbu t0, 839(a5)
	or s6, s6, t0
	lbu s7, 840(a5)
	slli s7, s7, 8
	lbu t0, 841(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 842(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 843(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 844(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 845(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 846(a5)
	or s7, s7, t0
	slli s7, s7, 8
	lbu t0, 847(a5)
	or s7, s7, t0
	addi t0, a3, -16
	beqz t0, 29f
	addi t0, s0, 0
	srli t1, t0, 56
	sb t1, 0(a2)
	srli t1, t0, 48
	sb t1, 1(a2)
	srli t1, t0, 40
	sb t1, 2(a2)
	srli t1, t0, 32
	sb t1, 3(a2)
	srli t1, t0, 24
	sb t1, 4(a2)
	srli t1, t0, 16
	sb t1, 5(a2)
	srli t1, t0, 8
	sb t1, 6(a2)
	srli t1, t0, 0
	sb t1, 7(a2)
	addi t0, s1, 0
	srli t1, t0, 56
	sb t1, 8(a2)
	srli t1, t0, 48
	sb t1, 9(a2)
	srli t1, t0, 40
	sb t1, 10(a2)
	srli t1, t0, 32
	sb t1, 11(a2)
	srli t1, t0, 24
	sb t1, 12(a2)
	srli t1, t0, 16
	sb t1, 13(a2)
	srli t1, t0, 8
	sb t1, 14(a2)
	srli t1, t0, 0
	sb t1, 15(a2)
	addi t0, s6, 0
	srli t1, t0, 56
	sb t1, 16(a2)
	srli t1, t0, 48
	sb t1, 17(a2)
	srli t1, t0, 40
	sb t1, 18(a2)
	srli t1, t0, 32
	sb t1, 19(a2)
	srli t1, t0, 24
	sb t1, 20(a2)
	srli t1, t0, 16
	sb t1, 21(a2)
	srli t1, t0, 8
	sb t1, 22(a2)
	srli t1, t0, 0
	sb t1, 23(a2)
	addi t0, s7, 0
	srli t1, t0, 56
	sb t1, 24(a2)
	srli t1, t0, 48
	sb t1, 25(a2)
	srli t1, t0, 40
	sb t1, 26(a2)
	srli t1, t0, 32
	sb t1, 27(a2)
	srli t1, t0, 24
	sb t1, 28(a2)
	srli t1, t0, 16
	sb t1, 29(a2)
	srli t1, t0, 8
	sb t1, 30(a2)
	srli t1, t0, 0
	sb t1, 31(a2)
	slli t0, s2, 15
	srli t1, s3, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 32(a2)
	srli t1, t0, 48
	sb t1, 33(a2)
	srli t1, t0, 40
	sb t1, 34(a2)
	srli t1, t0, 32
	sb t1, 35(a2)
	srli t1, t0, 24
	sb t1, 36(a2)
	srli t1, t0, 16
	sb t1, 37(a2)
	srli t1, t0, 8
	sb t1, 38(a2)
	srli t1, t0, 0
	sb t1, 39(a2)
	slli t0, s3, 15
	srli t1, s2, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 40(a2)
	srli t1, t0, 48
	sb t1, 41(a2)
	srli t1, t0, 40
	sb t1, 42(a2)
	srli t1, t0, 32
	sb t1, 43(a2)
	srli t1, t0, 24
	sb t1, 44(a2)
	srli t1, t0, 16
	sb t1, 45(a2)
	srli t1, t0, 8
	sb t1, 46(a2)
	srli t1, t0, 0
	sb t1, 47(a2)
	slli t0, s4, 15
	srli t1, s5, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 48(a2)
	srli t1, t0, 48
	sb t1, 49(a2)
	srli t1, t0, 40
	sb t1, 50(a2)
	srli t1, t0, 32
	sb t1, 51(a2)
	srli t1, t0, 24
	sb t1, 52(a2)
	srli t1, t0, 16
	sb t1, 53(a2)
	srli t1, t0, 8
	sb t1, 54(a2)
	srli t1, t0, 0
	sb t1, 55(a2)
	slli t0, s5, 15
	srli t1, s4, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 56(a2)
	srli t1, t0, 48
	sb t1, 57(a2)
	srli t1, t0, 40
	sb t1, 58(a2)
	srli t1, t0, 32
	sb t1, 59(a2)
	srli t1, t0, 24
	sb t1, 60(a2)
	srli t1, t0, 16
	sb t1, 61(a2)
	srli t1, t0, 8
	sb t1, 62(a2)
	srli t1, t0, 0
	sb t1, 63(a2)
	slli t0, s2, 30
	srli t1, s3, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 64(a2)
	srli t1, t0, 48
	sb t1, 65(a2)
	srli t1, t0, 40
	sb t1, 66(a2)
	srli t1, t0, 32
	sb t1, 67(a2)
	srli t1, t0, 24
	sb t1, 68(a2)
	srli t1, t0, 16
	sb t1, 69(a2)
	srli t1, t0, 8
	sb t1, 70(a2)
	srli t1, t0, 0
	sb t1, 71(a2)
	slli t0, s3, 30
	srli t1, s2, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 72(a2)
	srli t1, t0, 48
	sb t1, 73(a2)
	srli t1, t0, 40
	sb t1, 74(a2)
	srli t1, t0, 32
	sb t1, 75(a2)
	srli t1, t0, 24
	sb t1, 76(a2)
	srli t1, t0, 16
	sb t1, 77(a2)
	srli t1, t0, 8
	sb t1, 78(a2)
	srli t1, t0, 0
	sb t1, 79(a2)
	slli t0, s6, 30
	srli t1, s7, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 80(a2)
	srli t1, t0, 48
	sb t1, 81(a2)
	srli t1, t0, 40
	sb t1, 82(a2)
	srli t1, t0, 32
	sb t1, 83(a2)
	srli t1, t0, 24
	sb t1, 84(a2)
	srli t1, t0, 16
	sb t1, 85(a2)
	srli t1, t0, 8
	sb t1, 86(a2)
	srli t1, t0, 0
	sb t1, 87(a2)
	slli t0, s7, 30
	srli t1, s6, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 88(a2)
	srli t1, t0, 48
	sb t1, 89(a2)
	srli t1, t0, 40
	sb t1, 90(a2)
	srli t1, t0, 32
	sb t1, 91(a2)
	srli t1, t0, 24
	sb t1, 92(a2)
	srli t1, t0, 16
	sb t1, 93(a2)
	srli t1, t0, 8
	sb t1, 94(a2)
	srli t1, t0, 0
	sb t1, 95(a2)
	slli t0, s0, 45
	srli t1, s1, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 96(a2)
	srli t1, t0, 48
	sb t1, 97(a2)
	srli t1, t0, 40
	sb t1, 98(a2)
	srli t1, t0, 32
	sb t1, 99(a2)
	srli t1, t0, 24
	sb t1, 100(a2)
	srli t1, t0, 16
	sb t1, 101(a2)
	srli t1, t0, 8
	sb t1, 102(a2)
	srli t1, t0, 0
	sb t1, 103(a2)
	slli t0, s1, 45
	srli t1, s0, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 104(a2)
	srli t1, t0, 48
	sb t1, 105(a2)
	srli t1, t0, 40
	sb t1, 106(a2)
	srli t1, t0, 32
	sb t1, 107(a2)
	srli t1, t0, 24
	sb t1, 108(a2)
	srli t1, t0, 16
	sb t1, 109(a2)
	srli t1, t0, 8
	sb t1, 110(a2)
	srli t1, t0, 0
	sb t1, 111(a2)
	slli t0, s4, 45
	srli t1, s5, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 112(a2)
	srli t1, t0, 48
	sb t1, 113(a2)
	srli t1, t0, 40
	sb t1, 114(a2)
	srli t1, t0, 32
	sb t1, 115(a2)
	srli t1, t0, 24
	sb t1, 116(a2)
	srli t1, t0, 16
	sb t1, 117(a2)
	srli t1, t0, 8
	sb t1, 118(a2)
	srli t1, t0, 0
	sb t1, 119(a2)
	slli t0, s5, 45
	srli t1, s4, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 120(a2)
	srli t1, t0, 48
	sb t1, 121(a2)
	srli t1, t0, 40
	sb t1, 122(a2)
	srli t1, t0, 32
	sb t1, 123(a2)
	srli t1, t0, 24
	sb t1, 124(a2)
	srli t1, t0, 16
	sb t1, 125(a2)
	srli t1, t0, 8
	sb t1, 126(a2)
	srli t1, t0, 0
	sb t1, 127(a2)
	slli t0, s0, 60
	srli t1, s1, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 128(a2)
	srli t1, t0, 48
	sb t1, 129(a2)
	srli t1, t0, 40
	sb t1, 130(a2)
	srli t1, t0, 32
	sb t1, 131(a2)
	srli t1, t0, 24
	sb t1, 132(a2)
	srli t1, t0, 16
	sb t1, 133(a2)
	srli t1, t0, 8
	sb t1, 134(a2)
	srli t1, t0, 0
	sb t1, 135(a2)
	slli t0, s1, 60
	srli t1, s0, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 136(a2)
	srli t1, t0, 48
	sb t1, 137(a2)
	srli t1, t0, 40
	sb t1, 138(a2)
	srli t1, t0, 32
	sb t1, 139(a2)
	srli t1, t0, 24
	sb t1, 140(a2)
	srli t1, t0, 16
	sb t1, 141(a2)
	srli t1, t0, 8
	sb t1, 142(a2)
	srli t1, t0, 0
	sb t1, 143(a2)
	slli t0, s2, 60
	srli t1, s3, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 144(a2)
	srli t1, t0, 48
	sb t1, 145(a2)
	srli t1, t0, 40
	sb t1, 146(a2)
	srli t1, t0, 32
	sb t1, 147(a2)
	srli t1, t0, 24
	sb t1, 148(a2)
	srli t1, t0, 16
	sb t1, 149(a2)
	srli t1, t0, 8
	sb t1, 150(a2)
	srli t1, t0, 0
	sb t1, 151(a2)
	slli t0, s3, 60
	srli t1, s2, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 152(a2)
	srli t1, t0, 48
	sb t1, 153(a2)
	srli t1, t0, 40
	sb t1, 154(a2)
	srli t1, t0, 32
	sb t1, 155(a2)
	srli t1, t0, 24
	sb t1, 156(a2)
	srli t1, t0, 16
	sb t1, 157(a2)
	srli t1, t0, 8
	sb t1, 158(a2)
	srli t1, t0, 0
	sb t1, 159(a2)
	slli t0, s6, 60
	srli t1, s7, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 160(a2)
	srli t1, t0, 48
	sb t1, 161(a2)
	srli t1, t0, 40
	sb t1, 162(a2)
	srli t1, t0, 32
	sb t1, 163(a2)
	srli t1, t0, 24
	sb t1, 164(a2)
	srli t1, t0, 16
	sb t1, 165(a2)
	srli t1, t0, 8
	sb t1, 166(a2)
	srli t1, t0, 0
	sb t1, 167(a2)
	slli t0, s7, 60
	srli t1, s6, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 168(a2)
	srli t1, t0, 48
	sb t1, 169(a2)
	srli t1, t0, 40
	sb t1, 170(a2)
	srli t1, t0, 32
	sb t1, 171(a2)
	srli t1, t0, 24
	sb t1, 172(a2)
	srli t1, t0, 16
	sb t1, 173(a2)
	srli t1, t0, 8
	sb t1, 174(a2)
	srli t1, t0, 0
	sb t1, 175(a2)
	slli t0, s1, 13
	srli t1, s0, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 176(a2)
	srli t1, t0, 48
	sb t1, 177(a2)
	srli t1, t0, 40
	sb t1, 178(a2)
	srli t1, t0, 32
	sb t1, 179(a2)
	srli t1, t0, 24
	sb t1, 180(a2)
	srli t1, t0, 16
	sb t1, 181(a2)
	srli t1, t0, 8
	sb t1, 182(a2)
	srli t1, t0, 0
	sb t1, 183(a2)
	slli t0, s0, 13
	srli t1, s1, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 184(a2)
	srli t1, t0, 48
	sb t1, 185(a2)
	srli t1, t0, 40
	sb t1, 186(a2)
	srli t1, t0, 32
	sb t1, 187(a2)
	srli t1, t0, 24
	sb t1, 188(a2)
	srli t1, t0, 16
	sb t1, 189(a2)
	srli t1, t0, 8
	sb t1, 190(a2)
	srli t1, t0, 0
	sb t1, 191(a2)
	slli t0, s5, 13
	srli t1, s4, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 192(a2)
	srli t1, t0, 48
	sb t1, 193(a2)
	srli t1, t0, 40
	sb t1, 194(a2)
	srli t1, t0, 32
	sb t1, 195(a2)
	srli t1, t0, 24
	sb t1, 196(a2)
	srli t1, t0, 16
	sb t1, 197(a2)
	srli t1, t0, 8
	sb t1, 198(a2)
	srli t1, t0, 0
	sb t1, 199(a2)
	slli t0, s4, 13
	srli t1, s5, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 200(a2)
	srli t1, t0, 48
	sb t1, 201(a2)
	srli t1, t0, 40
	sb t1, 202(a2)
	srli t1, t0, 32
	sb t1, 203(a2)
	srli t1, t0, 24
	sb t1, 204(a2)
	srli t1, t0, 16
	sb t1, 205(a2)
	srli t1, t0, 8
	sb t1, 206(a2)
	srli t1, t0, 0
	sb t1, 207(a2)
	slli t0, s3, 30
	srli t1, s2, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 208(a2)
	srli t1, t0, 48
	sb t1, 209(a2)
	srli t1, t0, 40
	sb t1, 210(a2)
	srli t1, t0, 32
	sb t1, 211(a2)
	srli t1, t0, 24
	sb t1, 212(a2)
	srli t1, t0, 16
	sb t1, 213(a2)
	srli t1, t0, 8
	sb t1, 214(a2)
	srli t1, t0, 0
	sb t1, 215(a2)
	slli t0, s2, 30
	srli t1, s3, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 216(a2)
	srli t1, t0, 48
	sb t1, 217(a2)
	srli t1, t0, 40
	sb t1, 218(a2)
	srli t1, t0, 32
	sb t1, 219(a2)
	srli t1, t0, 24
	sb t1, 220(a2)
	srli t1, t0, 16
	sb t1, 221(a2)
	srli t1, t0, 8
	sb t1, 222(a2)
	srli t1, t0, 0
	sb t1, 223(a2)
	slli t0, s5, 30
	srli t1, s4, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 224(a2)
	srli t1, t0, 48
	sb t1, 225(a2)
	srli t1, t0, 40
	sb t1, 226(a2)
	srli t1, t0, 32
	sb t1, 227(a2)
	srli t1, t0, 24
	sb t1, 228(a2)
	srli t1, t0, 16
	sb t1, 229(a2)
	srli t1, t0, 8
	sb t1, 230(a2)
	srli t1, t0, 0
	sb t1, 231(a2)
	slli t0, s4, 30
	srli t1, s5, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 232(a2)
	srli t1, t0, 48
	sb t1, 233(a2)
	srli t1, t0, 40
	sb t1, 234(a2)
	srli t1, t0, 32
	sb t1, 235(a2)
	srli t1, t0, 24
	sb t1, 236(a2)
	srli t1, t0, 16
	sb t1, 237(a2)
	srli t1, t0, 8
	sb t1, 238(a2)
	srli t1, t0, 0
	sb t1, 239(a2)
	slli t0, s1, 47
	srli t1, s0, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 240(a2)
	srli t1, t0, 48
	sb t1, 241(a2)
	srli t1, t0, 40
	sb t1, 242(a2)
	srli t1, t0, 32
	sb t1, 243(a2)
	srli t1, t0, 24
	sb t1, 244(a2)
	srli t1, t0, 16
	sb t1, 245(a2)
	srli t1, t0, 8
	sb t1, 246(a2)
	srli t1, t0, 0
	sb t1, 247(a2)
	slli t0, s0, 47
	srli t1, s1, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 248(a2)
	srli t1, t0, 48
	sb t1, 249(a2)
	srli t1, t0, 40
	sb t1, 250(a2)
	srli t1, t0, 32
	sb t1, 251(a2)
	srli t1, t0, 24
	sb t1, 252(a2)
	srli t1, t0, 16
	sb t1, 253(a2)
	srli t1, t0, 8
	sb t1, 254(a2)
	srli t1, t0, 0
	sb t1, 255(a2)
	slli t0, s7, 47
	srli t1, s6, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 256(a2)
	srli t1, t0, 48
	sb t1, 257(a2)
	srli t1, t0, 40
	sb t1, 258(a2)
	srli t1, t0, 32
	sb t1, 259(a2)
	srli t1, t0, 24
	sb t1, 260(a2)
	srli t1, t0, 16
	sb t1, 261(a2)
	srli t1, t0, 8
	sb t1, 262(a2)
	srli t1, t0, 0
	sb t1, 263(a2)
	slli t0, s6, 47
	srli t1, s7, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 264(a2)
	srli t1, t0, 48
	sb t1, 265(a2)
	srli t1, t0, 40
	sb t1, 266(a2)
	srli t1, t0, 32
	sb t1, 267(a2)
	srli t1, t0, 24
	sb t1, 268(a2)
	srli t1, t0, 16
	sb t1, 269(a2)
	srli t1, t0, 8
	sb t1, 270(a2)
	srli t1, t0, 0
	sb t1, 271(a2)
	j 210f
29:
	addi t0, s0, 0
	srli t1, t0, 56
	sb t1, 0(a2)
	srli t1, t0, 48
	sb t1, 1(a2)
	srli t1, t0, 40
	sb t1, 2(a2)
	srli t1, t0, 32
	sb t1, 3(a2)
	srli t1, t0, 24
	sb t1, 4(a2)
	srli t1, t0, 16
	sb t1, 5(a2)
	srli t1, t0, 8
	sb t1, 6(a2)
	srli t1, t0, 0
	sb t1, 7(a2)
	addi t0, s1, 0
	srli t1, t0, 56
	sb t1, 8(a2)
	srli t1, t0, 48
	sb t1, 9(a2)
	srli t1, t0, 40
	sb t1, 10(a2)
	srli t1, t0, 32
	sb t1, 11(a2)
	srli t1, t0, 24
	sb t1, 12(a2)
	srli t1, t0, 16
	sb t1, 13(a2)
	srli t1, t0, 8
	sb t1, 14(a2)
	srli t1, t0, 0
	sb t1, 15(a2)
	addi t0, s4, 0
	srli t1, t0, 56
	sb t1, 16(a2)
	srli t1, t0, 48
	sb t1, 17(a2)
	srli t1, t0, 40
	sb t1, 18(a2)
	srli t1, t0, 32
	sb t1, 19(a2)
	srli t1, t0, 24
	sb t1, 20(a2)
	srli t1, t0, 16
	sb t1, 21(a2)
	srli t1, t0, 8
	sb t1, 22(a2)
	srli t1, t0, 0
	sb t1, 23(a2)
	addi t0, s5, 0
	srli t1, t0, 56
	sb t1, 24(a2)
	srli t1, t0, 48
	sb t1, 25(a2)
	srli t1, t0, 40
	sb t1, 26(a2)
	srli t1, t0, 32
	sb t1, 27(a2)
	srli t1, t0, 24
	sb t1, 28(a2)
	srli t1, t0, 16
	sb t1, 29(a2)
	srli t1, t0, 8
	sb t1, 30(a2)
	srli t1, t0, 0
	sb t1, 31(a2)
	slli t0, s0, 15
	srli t1, s1, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 32(a2)
	srli t1, t0, 48
	sb t1, 33(a2)
	srli t1, t0, 40
	sb t1, 34(a2)
	srli t1, t0, 32
	sb t1, 35(a2)
	srli t1, t0, 24
	sb t1, 36(a2)
	srli t1, t0, 16
	sb t1, 37(a2)
	srli t1, t0, 8
	sb t1, 38(a2)
	srli t1, t0, 0
	sb t1, 39(a2)
	slli t0, s1, 15
	srli t1, s0, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 40(a2)
	srli t1, t0, 48
	sb t1, 41(a2)
	srli t1, t0, 40
	sb t1, 42(a2)
	srli t1, t0, 32
	sb t1, 43(a2)
	srli t1, t0, 24
	sb t1, 44(a2)
	srli t1, t0, 16
	sb t1, 45(a2)
	srli t1, t0, 8
	sb t1, 46(a2)
	srli t1, t0, 0
	sb t1, 47(a2)
	slli t0, s4, 15
	srli t1, s5, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 48(a2)
	srli t1, t0, 48
	sb t1, 49(a2)
	srli t1, t0, 40
	sb t1, 50(a2)
	srli t1, t0, 32
	sb t1, 51(a2)
	srli t1, t0, 24
	sb t1, 52(a2)
	srli t1, t0, 16
	sb t1, 53(a2)
	srli t1, t0, 8
	sb t1, 54(a2)
	srli t1, t0, 0
	sb t1, 55(a2)
	slli t0, s5, 15
	srli t1, s4, 49
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 56(a2)
	srli t1, t0, 48
	sb t1, 57(a2)
	srli t1, t0, 40
	sb t1, 58(a2)
	srli t1, t0, 32
	sb t1, 59(a2)
	srli t1, t0, 24
	sb t1, 60(a2)
	srli t1, t0, 16
	sb t1, 61(a2)
	srli t1, t0, 8
	sb t1, 62(a2)
	srli t1, t0, 0
	sb t1, 63(a2)
	slli t0, s4, 30
	srli t1, s5, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 64(a2)
	srli t1, t0, 48
	sb t1, 65(a2)
	srli t1, t0, 40
	sb t1, 66(a2)
	srli t1, t0, 32
	sb t1, 67(a2)
	srli t1, t0, 24
	sb t1, 68(a2)
	srli t1, t0, 16
	sb t1, 69(a2)
	srli t1, t0, 8
	sb t1, 70(a2)
	srli t1, t0, 0
	sb t1, 71(a2)
	slli t0, s5, 30
	srli t1, s4, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 72(a2)
	srli t1, t0, 48
	sb t1, 73(a2)
	srli t1, t0, 40
	sb t1, 74(a2)
	srli t1, t0, 32
	sb t1, 75(a2)
	srli t1, t0, 24
	sb t1, 76(a2)
	srli t1, t0, 16
	sb t1, 77(a2)
	srli t1, t0, 8
	sb t1, 78(a2)
	srli t1, t0, 0
	sb t1, 79(a2)
	slli t0, s0, 45
	srli t1, s1, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 80(a2)
	srli t1, t0, 48
	sb t1, 81(a2)
	srli t1, t0, 40
	sb t1, 82(a2)
	srli t1, t0, 32
	sb t1, 83(a2)
	srli t1, t0, 24
	sb t1, 84(a2)
	srli t1, t0, 16
	sb t1, 85(a2)
	srli t1, t0, 8
	sb t1, 86(a2)
	srli t1, t0, 0
	sb t1, 87(a2)
	slli t0, s1, 45
	srli t1, s0, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 88(a2)
	srli t1, t0, 48
	sb t1, 89(a2)
	srli t1, t0, 40
	sb t1, 90(a2)
	srli t1, t0, 32
	sb t1, 91(a2)
	srli t1, t0, 24
	sb t1, 92(a2)
	srli t1, t0, 16
	sb t1, 93(a2)
	srli t1, t0, 8
	sb t1, 94(a2)
	srli t1, t0, 0
	sb t1, 95(a2)
	slli t0, s4, 45
	srli t1, s5, 19
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 96(a2)
	srli t1, t0, 48
	sb t1, 97(a2)
	srli t1, t0, 40
	sb t1, 98(a2)
	srli t1, t0, 32
	sb t1, 99(a2)
	srli t1, t0, 24
	sb t1, 100(a2)
	srli t1, t0, 16
	sb t1, 101(a2)
	srli t1, t0, 8
	sb t1, 102(a2)
	srli t1, t0, 0
	sb t1, 103(a2)
	slli t0, s1, 60
	srli t1, s0, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 104(a2)
	srli t1, t0, 48
	sb t1, 105(a2)
	srli t1, t0, 40
	sb t1, 106(a2)
	srli t1, t0, 32
	sb t1, 107(a2)
	srli t1, t0, 24
	sb t1, 108(a2)
	srli t1, t0, 16
	sb t1, 109(a2)
	srli t1, t0, 8
	sb t1, 110(a2)
	srli t1, t0, 0
	sb t1, 111(a2)
	slli t0, s4, 60
	srli t1, s5, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 112(a2)
	srli t1, t0, 48
	sb t1, 113(a2)
	srli t1, t0, 40
	sb t1, 114(a2)
	srli t1, t0, 32
	sb t1, 115(a2)
	srli t1, t0, 24
	sb t1, 116(a2)
	srli t1, t0, 16
	sb t1, 117(a2)
	srli t1, t0, 8
	sb t1, 118(a2)
	srli t1, t0, 0
	sb t1, 119(a2)
	slli t0, s5, 60
	srli t1, s4, 4
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 120(a2)
	srli t1, t0, 48
	sb t1, 121(a2)
	srli t1, t0, 40
	sb t1, 122(a2)
	srli t1, t0, 32
	sb t1, 123(a2)
	srli t1, t0, 24
	sb t1, 124(a2)
	srli t1, t0, 16
	sb t1, 125(a2)
	srli t1, t0, 8
	sb t1, 126(a2)
	srli t1, t0, 0
	sb t1, 127(a2)
	slli t0, s1, 13
	srli t1, s0, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 128(a2)
	srli t1, t0, 48
	sb t1, 129(a2)
	srli t1, t0, 40
	sb t1, 130(a2)
	srli t1, t0, 32
	sb t1, 131(a2)
	srli t1, t0, 24
	sb t1, 132(a2)
	srli t1, t0, 16
	sb t1, 133(a2)
	srli t1, t0, 8
	sb t1, 134(a2)
	srli t1, t0, 0
	sb t1, 135(a2)
	slli t0, s0, 13
	srli t1, s1, 51
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 136(a2)
	srli t1, t0, 48
	sb t1, 137(a2)
	srli t1, t0, 40
	sb t1, 138(a2)
	srli t1, t0, 32
	sb t1, 139(a2)
	srli t1, t0, 24
	sb t1, 140(a2)
	srli t1, t0, 16
	sb t1, 141(a2)
	srli t1, t0, 8
	sb t1, 142(a2)
	srli t1, t0, 0
	sb t1, 143(a2)
	slli t0, s1, 30
	srli t1, s0, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 144(a2)
	srli t1, t0, 48
	sb t1, 145(a2)
	srli t1, t0, 40
	sb t1, 146(a2)
	srli t1, t0, 32
	sb t1, 147(a2)
	srli t1, t0, 24
	sb t1, 148(a2)
	srli t1, t0, 16
	sb t1, 149(a2)
	srli t1, t0, 8
	sb t1, 150(a2)
	srli t1, t0, 0
	sb t1, 151(a2)
	slli t0, s0, 30
	srli t1, s1, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 152(a2)
	srli t1, t0, 48
	sb t1, 153(a2)
	srli t1, t0, 40
	sb t1, 154(a2)
	srli t1, t0, 32
	sb t1, 155(a2)
	srli t1, t0, 24
	sb t1, 156(a2)
	srli t1, t0, 16
	sb t1, 157(a2)
	srli t1, t0, 8
	sb t1, 158(a2)
	srli t1, t0, 0
	sb t1, 159(a2)
	slli t0, s5, 30
	srli t1, s4, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 160(a2)
	srli t1, t0, 48
	sb t1, 161(a2)
	srli t1, t0, 40
	sb t1, 162(a2)
	srli t1, t0, 32
	sb t1, 163(a2)
	srli t1, t0, 24
	sb t1, 164(a2)
	srli t1, t0, 16
	sb t1, 165(a2)
	srli t1, t0, 8
	sb t1, 166(a2)
	srli t1, t0, 0
	sb t1, 167(a2)
	slli t0, s4, 30
	srli t1, s5, 34
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 168(a2)
	srli t1, t0, 48
	sb t1, 169(a2)
	srli t1, t0, 40
	sb t1, 170(a2)
	srli t1, t0, 32
	sb t1, 171(a2)
	srli t1, t0, 24
	sb t1, 172(a2)
	srli t1, t0, 16
	sb t1, 173(a2)
	srli t1, t0, 8
	sb t1, 174(a2)
	srli t1, t0, 0
	sb t1, 175(a2)
	slli t0, s1, 47
	srli t1, s0, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 176(a2)
	srli t1, t0, 48
	sb t1, 177(a2)
	srli t1, t0, 40
	sb t1, 178(a2)
	srli t1, t0, 32
	sb t1, 179(a2)
	srli t1, t0, 24
	sb t1, 180(a2)
	srli t1, t0, 16
	sb t1, 181(a2)
	srli t1, t0, 8
	sb t1, 182(a2)
	srli t1, t0, 0
	sb t1, 183(a2)
	slli t0, s0, 47
	srli t1, s1, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 184(a2)
	srli t1, t0, 48
	sb t1, 185(a2)
	srli t1, t0, 40
	sb t1, 186(a2)
	srli t1, t0, 32
	sb t1, 187(a2)
	srli t1, t0, 24
	sb t1, 188(a2)
	srli t1, t0, 16
	sb t1, 189(a2)
	srli t1, t0, 8
	sb t1, 190(a2)
	srli t1, t0, 0
	sb t1, 191(a2)
	slli t0, s5, 47
	srli t1, s4, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 192(a2)
	srli t1, t0, 48
	sb t1, 193(a2)
	srli t1, t0, 40
	sb t1, 194(a2)
	srli t1, t0, 32
	sb t1, 195(a2)
	srli t1, t0, 24
	sb t1, 196(a2)
	srli t1, t0, 16
	sb t1, 197(a2)
	srli t1, t0, 8
	sb t1, 198(a2)
	srli t1, t0, 0
	sb t1, 199(a2)
	slli t0, s4, 47
	srli t1, s5, 17
	or t0, t0, t1
	srli t1, t0, 56
	sb t1, 200(a2)
	srli t1, t0, 48
	sb t1, 201(a2)
	srli t1, t0, 40
	sb t1, 202(a2)
	srli t1, t0, 32
	sb t1, 203(a2)
	srli t1, t0, 24
	sb t1, 204(a2)
	srli t1, t0, 16
	sb t1, 205(a2)
	srli t1, t0, 8
	sb t1, 206(a2)
	srli t1, t0, 0
	sb t1, 207(a2)
210:
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	ld s8, 704(a5)
	ld s9, 712(a5)
	ld s10, 720(a5)
	ld s11, 728(a5)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	sd t6, 1152(t5)
	sd t6, 1160(t5)
	sd t6, 1168(t5)
	sd t6, 1176(t5)
	sd t6, 1184(t5)
	sd t6, 1192(t5)
	sd t6, 1200(t5)
	sd t6, 1208(t5)
	sd t6, 1216(t5)
	sd t6, 1224(t5)
	sd t6, 1232(t5)
	sd t6, 1240(t5)
	sd t6, 1248(t5)
	sd t6, 1256(t5)
	sd t6, 1264(t5)
	sd t6, 1272(t5)
	sd t6, 1280(t5)
	sd t6, 1288(t5)
	sd t6, 1296(t5)
	sd t6, 1304(t5)
	sd t6, 1312(t5)
	sd t6, 1320(t5)
	sd t6, 1328(t5)
	sd t6, 1336(t5)
	sd t6, 1344(t5)
	sd t6, 1352(t5)
	sd t6, 1360(t5)
	sd t6, 1368(t5)
	sd t6, 1376(t5)
	sd t6, 1384(t5)
	sd t6, 1392(t5)
	sd t6, 1400(t5)
	sd t6, 1408(t5)
	sd t6, 1416(t5)
	sd t6, 1424(t5)
	sd t6, 1432(t5)
	sd t6, 1440(t5)
	sd t6, 1448(t5)
	sd t6, 1456(t5)
	sd t6, 1464(t5)
	sd t6, 1472(t5)
	sd t6, 1480(t5)
	sd t6, 1488(t5)
	sd t6, 1496(t5)
	sd t6, 1504(t5)
	sd t6, 1512(t5)
	sd t6, 1520(t5)
	sd t6, 1528(t5)
	sd t6, 1536(t5)
	sd t6, 1544(t5)
	sd t6, 1552(t5)
	sd t6, 1560(t5)
	sd t6, 1568(t5)
	sd t6, 1576(t5)
	sd t6, 1584(t5)
	sd t6, 1592(t5)
	sd t6, 1600(t5)
	sd t6, 1608(t5)
	sd t6, 1616(t5)
	sd t6, 1624(t5)
	sd t6, 1632(t5)
	sd t6, 1640(t5)
	sd t6, 1648(t5)
	sd t6, 1656(t5)
	sd t6, 1664(t5)
	sd t6, 1672(t5)
	sd t6, 1680(t5)
	sd t6, 1688(t5)
	sd t6, 1696(t5)
	sd t6, 1704(t5)
	sd t6, 1712(t5)
	sd t6, 1720(t5)
	sd t6, 1728(t5)
	sd t6, 1736(t5)
	sd t6, 1744(t5)
	sd t6, 1752(t5)
	sd t6, 1760(t5)
	sd t6, 1768(t5)
	sd t6, 1776(t5)
	sd t6, 1784(t5)
	sd t6, 1792(t5)
	sd t6, 1800(t5)
	sd t6, 1808(t5)
	sd t6, 1816(t5)
	sd t6, 1824(t5)
	sd t6, 1832(t5)
	sd t6, 1840(t5)
	sd t6, 1848(t5)
	sd t6, 1856(t5)
	sd t6, 1864(t5)
	sd t6, 1872(t5)
	sd t6, 1880(t5)
	sd t6, 1888(t5)
	sd t6, 1896(t5)
	sd t6, 1904(t5)
	sd t6, 1912(t5)
	sd t6, 1920(t5)
	sd t6, 1928(t5)
	sd t6, 1936(t5)
	sd t6, 1944(t5)
	sd t6, 1952(t5)
	sd t6, 1960(t5)
	sd t6, 1968(t5)
	sd t6, 1976(t5)
	sd t6, 1984(t5)
	sd t6, 1992(t5)
	sd t6, 2000(t5)
	sd t6, 2008(t5)
	sd t6, 2016(t5)
	sd t6, 2024(t5)
	sd t6, 2032(t5)
	sd t6, 2040(t5)
	addi t5, t5, 1024
	addi t5, t5, 1024
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	addi sp, sp, 1168
	addi sp, sp, 2032
	ret
	.option pop

vg_camellia_ecb_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1168
	addi a4, sp, 0
	addi a5, a4, 0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	sd s8, 704(a5)
	sd s9, 712(a5)
	sd s10, 720(a5)
	sd s11, 728(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 384(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 392(a5)
	lui t0, 4096
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 400(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 408(a5)
	lui t0, 0
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 464(a5)
	addi t0, a1, -18
	beqz t0, 20f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi t1, zero, 34
	j 21f
20:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi t1, zero, 26
21:
	addi a1, a5, 1024
22:
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	addi a0, a0, 8
	addi t1, t1, -1
	bnez t1, 22b
	beqz a3, 23f
25:
	srli t0, a3, 3
	bnez t0, 26f
	addi t6, a3, 0
	j 27f
26:
	addi t6, zero, 8
27:
	addi t3, a2, 0
	addi t4, a5, 768
	addi t5, t6, 0
28:
	lbu t0, 0(t3)
	lbu t1, 1(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(t3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(t3)
	lbu t1, 5(t3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(t3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(t3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 0(t4)
	lbu t0, 8(t3)
	lbu t1, 9(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(t3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(t3)
	lbu t1, 13(t3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(t3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(t3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 8(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 28b
	addi a1, a5, 1024
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld t0, 576(a5)
	ld t3, 64(a1)
	xor t0, t0, t3
	sd t0, 576(a5)
	ld t0, 584(a5)
	ld t3, 72(a1)
	xor t0, t0, t3
	sd t0, 584(a5)
	ld t0, 592(a5)
	ld t3, 80(a1)
	xor t0, t0, t3
	sd t0, 592(a5)
	ld t0, 600(a5)
	ld t3, 88(a1)
	xor t0, t0, t3
	sd t0, 600(a5)
	ld t0, 608(a5)
	ld t3, 96(a1)
	xor t0, t0, t3
	sd t0, 608(a5)
	ld t0, 616(a5)
	ld t3, 104(a1)
	xor t0, t0, t3
	sd t0, 616(a5)
	ld t0, 624(a5)
	ld t3, 112(a1)
	xor t0, t0, t3
	sd t0, 624(a5)
	ld t0, 632(a5)
	ld t3, 120(a1)
	xor t0, t0, t3
	sd t0, 632(a5)
	addi a1, a1, 128
29:
	addi a0, a1, 384
210:
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	sd s0, 576(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	sd s1, 584(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	sd s2, 592(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	sd s3, 600(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	sd s4, 608(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	sd s5, 616(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	sd s6, 624(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	sd s7, 632(a5)
	ld t0, 64(a1)
	xor s0, s0, t0
	ld t0, 72(a1)
	xor s1, s1, t0
	ld t0, 80(a1)
	xor s2, s2, t0
	ld t0, 88(a1)
	xor s3, s3, t0
	ld t0, 96(a1)
	xor s4, s4, t0
	ld t0, 104(a1)
	xor s5, s5, t0
	ld t0, 112(a1)
	xor s6, s6, t0
	ld t0, 120(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	sd s0, 512(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	sd s1, 520(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	sd s2, 528(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	sd s3, 536(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	sd s4, 544(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	sd s5, 552(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	sd s6, 560(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	sd s7, 568(a5)
	addi a1, a1, 128
	sub t0, a1, a0
	bnez t0, 210b
	sub t0, a1, a4
	bnez t0, 211f
	j 212f
211:
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	ld t2, 384(a5)
	ld t3, 120(a1)
	or t0, s7, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 112(a1)
	or t0, s6, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 104(a1)
	or t0, s5, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 96(a1)
	or t0, s4, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 88(a1)
	or t0, s3, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 80(a1)
	or t0, s2, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 72(a1)
	or t0, s1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 64(a1)
	or t0, s0, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 392(a5)
	addi t1, s7, 0
	ld t3, 112(a1)
	and t0, s6, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 104(a1)
	and t0, s5, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 96(a1)
	and t0, s4, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 88(a1)
	and t0, s3, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 80(a1)
	and t0, s2, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 72(a1)
	and t0, s1, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 64(a1)
	and t0, s0, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 120(a1)
	and t0, t1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 512(a5)
	ld s1, 520(a5)
	ld s2, 528(a5)
	ld s3, 536(a5)
	ld s4, 544(a5)
	ld s5, 552(a5)
	ld s6, 560(a5)
	ld s7, 568(a5)
	ld t2, 392(a5)
	addi t1, s7, 0
	ld t3, 48(a1)
	and t0, s6, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 40(a1)
	and t0, s5, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 32(a1)
	and t0, s4, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 24(a1)
	and t0, s3, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 16(a1)
	and t0, s2, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 8(a1)
	and t0, s1, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 0(a1)
	and t0, s0, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 56(a1)
	and t0, t1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 384(a5)
	ld t3, 56(a1)
	or t0, s7, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 48(a1)
	or t0, s6, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 40(a1)
	or t0, s5, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 32(a1)
	or t0, s4, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 24(a1)
	or t0, s3, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 16(a1)
	or t0, s2, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 8(a1)
	or t0, s1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 0(a1)
	or t0, s0, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	addi a1, a1, 128
212:
	sub t0, a1, a4
	bnez t0, 29b
	ld t0, 64(a1)
	xor s0, s0, t0
	ld t0, 72(a1)
	xor s1, s1, t0
	ld t0, 80(a1)
	xor s2, s2, t0
	ld t0, 88(a1)
	xor s3, s3, t0
	ld t0, 96(a1)
	xor s4, s4, t0
	ld t0, 104(a1)
	xor s5, s5, t0
	ld t0, 112(a1)
	xor s6, s6, t0
	ld t0, 120(a1)
	xor s7, s7, t0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 776(a5)
	sd s1, 792(a5)
	sd s2, 808(a5)
	sd s3, 824(a5)
	sd s4, 840(a5)
	sd s5, 856(a5)
	sd s6, 872(a5)
	sd s7, 888(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 768(a5)
	sd s1, 784(a5)
	sd s2, 800(a5)
	sd s3, 816(a5)
	sd s4, 832(a5)
	sd s5, 848(a5)
	sd s6, 864(a5)
	sd s7, 880(a5)
	srli t0, a3, 3
	bnez t0, 213f
	addi t6, a3, 0
	j 214f
213:
	addi t6, zero, 8
214:
	addi t3, a5, 768
	addi t4, a2, 0
	addi t5, t6, 0
215:
	ld t0, 0(t3)
	sb t0, 0(t4)
	srli t1, t0, 8
	sb t1, 1(t4)
	srli t1, t0, 16
	sb t1, 2(t4)
	srli t1, t0, 24
	sb t1, 3(t4)
	srli t1, t0, 32
	sb t1, 4(t4)
	srli t2, t1, 8
	sb t2, 5(t4)
	srli t2, t1, 16
	sb t2, 6(t4)
	srli t2, t1, 24
	sb t2, 7(t4)
	ld t0, 8(t3)
	sb t0, 8(t4)
	srli t1, t0, 8
	sb t1, 9(t4)
	srli t1, t0, 16
	sb t1, 10(t4)
	srli t1, t0, 24
	sb t1, 11(t4)
	srli t1, t0, 32
	sb t1, 12(t4)
	srli t2, t1, 8
	sb t2, 13(t4)
	srli t2, t1, 16
	sb t2, 14(t4)
	srli t2, t1, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 215b
	sub a3, a3, t6
	addi a2, a2, 128
	bnez a3, 25b
	j 24f
23:
24:
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	ld s8, 704(a5)
	ld s9, 712(a5)
	ld s10, 720(a5)
	ld s11, 728(a5)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	sd t6, 1152(t5)
	sd t6, 1160(t5)
	sd t6, 1168(t5)
	sd t6, 1176(t5)
	sd t6, 1184(t5)
	sd t6, 1192(t5)
	sd t6, 1200(t5)
	sd t6, 1208(t5)
	sd t6, 1216(t5)
	sd t6, 1224(t5)
	sd t6, 1232(t5)
	sd t6, 1240(t5)
	sd t6, 1248(t5)
	sd t6, 1256(t5)
	sd t6, 1264(t5)
	sd t6, 1272(t5)
	sd t6, 1280(t5)
	sd t6, 1288(t5)
	sd t6, 1296(t5)
	sd t6, 1304(t5)
	sd t6, 1312(t5)
	sd t6, 1320(t5)
	sd t6, 1328(t5)
	sd t6, 1336(t5)
	sd t6, 1344(t5)
	sd t6, 1352(t5)
	sd t6, 1360(t5)
	sd t6, 1368(t5)
	sd t6, 1376(t5)
	sd t6, 1384(t5)
	sd t6, 1392(t5)
	sd t6, 1400(t5)
	sd t6, 1408(t5)
	sd t6, 1416(t5)
	sd t6, 1424(t5)
	sd t6, 1432(t5)
	sd t6, 1440(t5)
	sd t6, 1448(t5)
	sd t6, 1456(t5)
	sd t6, 1464(t5)
	sd t6, 1472(t5)
	sd t6, 1480(t5)
	sd t6, 1488(t5)
	sd t6, 1496(t5)
	sd t6, 1504(t5)
	sd t6, 1512(t5)
	sd t6, 1520(t5)
	sd t6, 1528(t5)
	sd t6, 1536(t5)
	sd t6, 1544(t5)
	sd t6, 1552(t5)
	sd t6, 1560(t5)
	sd t6, 1568(t5)
	sd t6, 1576(t5)
	sd t6, 1584(t5)
	sd t6, 1592(t5)
	sd t6, 1600(t5)
	sd t6, 1608(t5)
	sd t6, 1616(t5)
	sd t6, 1624(t5)
	sd t6, 1632(t5)
	sd t6, 1640(t5)
	sd t6, 1648(t5)
	sd t6, 1656(t5)
	sd t6, 1664(t5)
	sd t6, 1672(t5)
	sd t6, 1680(t5)
	sd t6, 1688(t5)
	sd t6, 1696(t5)
	sd t6, 1704(t5)
	sd t6, 1712(t5)
	sd t6, 1720(t5)
	sd t6, 1728(t5)
	sd t6, 1736(t5)
	sd t6, 1744(t5)
	sd t6, 1752(t5)
	sd t6, 1760(t5)
	sd t6, 1768(t5)
	sd t6, 1776(t5)
	sd t6, 1784(t5)
	sd t6, 1792(t5)
	sd t6, 1800(t5)
	sd t6, 1808(t5)
	sd t6, 1816(t5)
	sd t6, 1824(t5)
	sd t6, 1832(t5)
	sd t6, 1840(t5)
	sd t6, 1848(t5)
	sd t6, 1856(t5)
	sd t6, 1864(t5)
	sd t6, 1872(t5)
	sd t6, 1880(t5)
	sd t6, 1888(t5)
	sd t6, 1896(t5)
	sd t6, 1904(t5)
	sd t6, 1912(t5)
	sd t6, 1920(t5)
	sd t6, 1928(t5)
	sd t6, 1936(t5)
	sd t6, 1944(t5)
	sd t6, 1952(t5)
	sd t6, 1960(t5)
	sd t6, 1968(t5)
	sd t6, 1976(t5)
	sd t6, 1984(t5)
	sd t6, 1992(t5)
	sd t6, 2000(t5)
	sd t6, 2008(t5)
	sd t6, 2016(t5)
	sd t6, 2024(t5)
	sd t6, 2032(t5)
	sd t6, 2040(t5)
	addi t5, t5, 1024
	addi t5, t5, 1024
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	addi sp, sp, 1168
	addi sp, sp, 2032
	ret
	.option pop

vg_camellia_ecb_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -1168
	addi a4, sp, 0
	addi a5, a4, 0
	sd s0, 640(a5)
	sd s1, 648(a5)
	sd s2, 656(a5)
	sd s3, 664(a5)
	sd s4, 672(a5)
	sd s5, 680(a5)
	sd s6, 688(a5)
	sd s7, 696(a5)
	sd s8, 704(a5)
	sd s9, 712(a5)
	sd s10, 720(a5)
	sd s11, 728(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 384(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 392(a5)
	lui t0, 4096
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 400(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 408(a5)
	lui t0, 0
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 464(a5)
	addi t0, a1, -18
	beqz t0, 20f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi a0, a0, 256
	addi t1, zero, 30
	j 21f
20:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi a0, a0, 192
	addi t1, zero, 22
21:
	addi a1, a5, 1024
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	lbu s0, 8(a0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 10(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 11(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 12(a0)
	lbu t0, 13(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 14(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 15(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	addi a0, a0, -8
22:
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	addi a0, a0, -8
	addi t1, t1, -1
	bnez t1, 22b
	addi a0, a0, -8
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	lbu s0, 8(a0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 10(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 11(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t2, 12(a0)
	lbu t0, 13(a0)
	slli t0, t0, 8
	or t2, t2, t0
	lbu t0, 14(a0)
	slli t0, t0, 16
	or t2, t2, t0
	lbu t0, 15(a0)
	slli t0, t0, 24
	or t2, t2, t0
	slli t2, t2, 32
	or s0, s0, t2
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s4, s0, 0
	addi s5, s0, 0
	addi s6, s0, 0
	addi s7, s0, 0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a1)
	sd s1, 8(a1)
	sd s2, 16(a1)
	sd s3, 24(a1)
	sd s4, 32(a1)
	sd s5, 40(a1)
	sd s6, 48(a1)
	sd s7, 56(a1)
	addi a1, a1, 64
	beqz a3, 23f
25:
	srli t0, a3, 3
	bnez t0, 26f
	addi t6, a3, 0
	j 27f
26:
	addi t6, zero, 8
27:
	addi t3, a2, 0
	addi t4, a5, 768
	addi t5, t6, 0
28:
	lbu t0, 0(t3)
	lbu t1, 1(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(t3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(t3)
	lbu t1, 5(t3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(t3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(t3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 0(t4)
	lbu t0, 8(t3)
	lbu t1, 9(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(t3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(t3)
	lbu t1, 13(t3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(t3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(t3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 8(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 28b
	addi a1, a5, 1024
	ld s0, 776(a5)
	ld s1, 792(a5)
	ld s2, 808(a5)
	ld s3, 824(a5)
	ld s4, 840(a5)
	ld s5, 856(a5)
	ld s6, 872(a5)
	ld s7, 888(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 768(a5)
	ld s1, 784(a5)
	ld s2, 800(a5)
	ld s3, 816(a5)
	ld s4, 832(a5)
	ld s5, 848(a5)
	ld s6, 864(a5)
	ld s7, 880(a5)
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	ld t0, 576(a5)
	ld t3, 64(a1)
	xor t0, t0, t3
	sd t0, 576(a5)
	ld t0, 584(a5)
	ld t3, 72(a1)
	xor t0, t0, t3
	sd t0, 584(a5)
	ld t0, 592(a5)
	ld t3, 80(a1)
	xor t0, t0, t3
	sd t0, 592(a5)
	ld t0, 600(a5)
	ld t3, 88(a1)
	xor t0, t0, t3
	sd t0, 600(a5)
	ld t0, 608(a5)
	ld t3, 96(a1)
	xor t0, t0, t3
	sd t0, 608(a5)
	ld t0, 616(a5)
	ld t3, 104(a1)
	xor t0, t0, t3
	sd t0, 616(a5)
	ld t0, 624(a5)
	ld t3, 112(a1)
	xor t0, t0, t3
	sd t0, 624(a5)
	ld t0, 632(a5)
	ld t3, 120(a1)
	xor t0, t0, t3
	sd t0, 632(a5)
	addi a1, a1, 128
29:
	addi a0, a1, 384
210:
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 576(a5)
	xor s0, s0, t0
	sd s0, 576(a5)
	ld t0, 584(a5)
	xor s1, s1, t0
	sd s1, 584(a5)
	ld t0, 592(a5)
	xor s2, s2, t0
	sd s2, 592(a5)
	ld t0, 600(a5)
	xor s3, s3, t0
	sd s3, 600(a5)
	ld t0, 608(a5)
	xor s4, s4, t0
	sd s4, 608(a5)
	ld t0, 616(a5)
	xor s5, s5, t0
	sd s5, 616(a5)
	ld t0, 624(a5)
	xor s6, s6, t0
	sd s6, 624(a5)
	ld t0, 632(a5)
	xor s7, s7, t0
	sd s7, 632(a5)
	ld t0, 64(a1)
	xor s0, s0, t0
	ld t0, 72(a1)
	xor s1, s1, t0
	ld t0, 80(a1)
	xor s2, s2, t0
	ld t0, 88(a1)
	xor s3, s3, t0
	ld t0, 96(a1)
	xor s4, s4, t0
	ld t0, 104(a1)
	xor s5, s5, t0
	ld t0, 112(a1)
	xor s6, s6, t0
	ld t0, 120(a1)
	xor s7, s7, t0
	ld t2, 400(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s7, s1
	xor t1, s5, s3
	xor t2, s2, t0
	xor t3, s6, s0
	xor t4, s0, t1
	xor t5, s4, s1
	xor t6, s4, t2
	xor a6, s6, t1
	xor a7, s2, t3
	xor s8, t2, t3
	xor s9, s7, s6
	xor s10, s7, t3
	xori s10, s10, -1
	xor s11, s6, s3
	sd s10, 0(a5)
	xor s10, s5, s1
	sd s7, 8(a5)
	xor s7, s5, s0
	xor s5, s5, t2
	xor t3, s4, t3
	xor s4, s4, s9
	xor s3, s3, s0
	xori s3, s3, -1
	xor s0, s2, t4
	xor s2, s2, t5
	xori s2, s2, -1
	xor s9, s1, a6
	xori s9, s9, -1
	sd s9, 16(a5)
	xor s9, t0, t4
	xor t0, t0, a6
	xor a6, t1, t5
	sd s9, 24(a5)
	xor s9, t1, t6
	xor t1, t1, s8
	sd t1, 32(a5)
	xor t1, t2, t4
	xori t1, t1, -1
	xor t2, t2, s11
	xori t2, t2, -1
	xor t4, t4, t5
	xori t4, t4, -1
	xor s7, t6, s7
	xori s7, s7, -1
	xor s10, a7, s10
	xori s10, s10, -1
	xor a7, a7, a6
	xori a7, a7, -1
	ld a6, 8(a5)
	xor t5, a6, s6
	xori t5, t5, -1
	xor t5, t5, s6
	xor a6, a6, s1
	xori a6, a6, -1
	and s1, s2, s4
	and s6, t5, s10
	xor s6, s6, s1
	and s11, t6, s7
	xor s11, s11, s1
	and s1, s0, t1
	sd s0, 8(a5)
	and s0, t0, s5
	xor s0, s0, s1
	sd t0, 40(a5)
	and t0, s8, s3
	xor t0, t0, s1
	and s1, t3, s9
	sd t3, 48(a5)
	and t3, t4, a7
	xor t3, t3, s1
	sd t4, 56(a5)
	ld t4, 16(a5)
	sd s8, 64(a5)
	ld s8, 0(a5)
	sd t6, 72(a5)
	and t6, t4, s8
	xor t6, t6, s1
	xor s6, s6, t3
	xor s11, s11, t6
	xor s0, s0, t3
	xor t0, t0, t6
	ld t6, 32(a5)
	xor s6, s6, t6
	ld t6, 24(a5)
	xor s11, s11, t6
	xor s0, s0, a6
	xor t0, t0, t2
	xor t2, s6, s11
	and s6, s6, s0
	xor a6, t0, s6
	and t6, t2, a6
	xor t6, t6, s11
	xor t3, s0, t0
	xor s11, s11, s6
	and s11, s11, t3
	xor s11, s11, t0
	xor s0, s0, s11
	xor t3, a6, s11
	and t0, t0, t3
	xor s0, t0, s0
	xor a6, a6, t0
	and a6, t6, a6
	xor t2, t2, a6
	xor a6, t2, s0
	xor t0, t6, s11
	xor t3, t6, t2
	xor s6, s11, s0
	xor s1, t0, a6
	and s4, s6, s4
	and s10, s0, s10
	and s7, s11, s7
	and t1, t3, t1
	and s5, t2, s5
	and s3, t6, s3
	and s9, t0, s9
	and a7, s1, a7
	and s8, a6, s8
	and s6, s6, s2
	and s0, s0, t5
	ld t5, 72(a5)
	and s11, s11, t5
	ld t5, 8(a5)
	and t3, t3, t5
	ld t5, 40(a5)
	and t2, t2, t5
	ld t5, 64(a5)
	and t6, t6, t5
	ld t5, 48(a5)
	and t0, t0, t5
	ld t5, 56(a5)
	and s1, s1, t5
	and a6, a6, t4
	xor a7, s10, a7
	xor t1, t1, s3
	xor t4, s9, s8
	xor t5, s4, s1
	xor s11, s11, a7
	xor s2, t3, t1
	sd t1, 16(a5)
	xor t1, t0, t4
	xor t6, s7, t6
	xor s9, s9, a6
	xor s8, s8, s6
	xor s6, s6, s0
	xor t2, t2, s2
	xor s1, s1, t1
	sd s1, 56(a5)
	xor s1, t5, s11
	xor s4, s4, s7
	xor s10, s10, s5
	xor s3, s3, t5
	xor s0, s0, s9
	xor t3, t3, s11
	xor t0, t0, a7
	xor a6, a6, s8
	ld a7, 16(a5)
	xor a7, a7, s6
	xor s4, t4, s4
	xor s2, s2, t6
	xor t1, t1, s6
	xor t6, t6, s8
	xor s9, s9, t0
	ld t0, 56(a5)
	xor s8, t2, t0
	xor t2, t2, s1
	xor s5, t0, a7
	xori s5, s5, -1
	xor s1, s1, s0
	xori s1, s1, -1
	xor s10, s10, s3
	xor s3, t3, t6
	xori s3, s3, -1
	xor a6, a6, t2
	xori a6, a6, -1
	xor s7, s2, s9
	xor s6, t1, s10
	xori s6, s6, -1
	addi s2, s1, 0
	addi s1, a6, 0
	addi s0, s8, 0
	ld t2, 408(a5)
	addi t1, s7, 0
	xor t0, s7, s6
	and t0, t0, t2
	xor s7, s7, t0
	xor t0, s6, s5
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s5, s4
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s4, s3
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s3, s2
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s2, s1
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s1, s0
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s0, t1
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 416(a5)
	addi t1, s0, 0
	xor t0, s0, s1
	and t0, t0, t2
	xor s0, s0, t0
	xor t0, s1, s2
	and t0, t0, t2
	xor s1, s1, t0
	xor t0, s2, s3
	and t0, t0, t2
	xor s2, s2, t0
	xor t0, s3, s4
	and t0, t0, t2
	xor s3, s3, t0
	xor t0, s4, s5
	and t0, t0, t2
	xor s4, s4, t0
	xor t0, s5, s6
	and t0, t0, t2
	xor s5, s5, t0
	xor t0, s6, s7
	and t0, t0, t2
	xor s6, s6, t0
	xor t0, s7, t1
	and t0, t0, t2
	xor s7, s7, t0
	ld t2, 384(a5)
	ld t3, 392(a5)
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s0, 56
	slli t0, s0, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 8
	slli t0, s0, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s0, s0, t0
	srli t4, s0, 40
	slli t0, s0, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s1, 56
	slli t0, s1, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 8
	slli t0, s1, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s1, s1, t0
	srli t4, s1, 40
	slli t0, s1, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s2, 56
	slli t0, s2, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 8
	slli t0, s2, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s2, s2, t0
	srli t4, s2, 40
	slli t0, s2, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s3, 56
	slli t0, s3, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 8
	slli t0, s3, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s3, s3, t0
	srli t4, s3, 40
	slli t0, s3, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s4, 56
	slli t0, s4, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 8
	slli t0, s4, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s4, s4, t0
	srli t4, s4, 40
	slli t0, s4, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s5, 56
	slli t0, s5, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 8
	slli t0, s5, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s5, s5, t0
	srli t4, s5, 40
	slli t0, s5, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s6, 56
	slli t0, s6, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 8
	slli t0, s6, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s6, s6, t0
	srli t4, s6, 40
	slli t0, s6, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	srli t4, s7, 56
	slli t0, s7, 8
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 8
	slli t0, s7, 56
	xor t0, t0, t4
	and t0, t0, t3
	xor s7, s7, t0
	srli t4, s7, 40
	slli t0, s7, 24
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t0, 512(a5)
	xor s0, s0, t0
	sd s0, 512(a5)
	ld t0, 520(a5)
	xor s1, s1, t0
	sd s1, 520(a5)
	ld t0, 528(a5)
	xor s2, s2, t0
	sd s2, 528(a5)
	ld t0, 536(a5)
	xor s3, s3, t0
	sd s3, 536(a5)
	ld t0, 544(a5)
	xor s4, s4, t0
	sd s4, 544(a5)
	ld t0, 552(a5)
	xor s5, s5, t0
	sd s5, 552(a5)
	ld t0, 560(a5)
	xor s6, s6, t0
	sd s6, 560(a5)
	ld t0, 568(a5)
	xor s7, s7, t0
	sd s7, 568(a5)
	addi a1, a1, 128
	sub t0, a1, a0
	bnez t0, 210b
	sub t0, a1, a4
	bnez t0, 211f
	j 212f
211:
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	ld t2, 384(a5)
	ld t3, 120(a1)
	or t0, s7, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 112(a1)
	or t0, s6, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 104(a1)
	or t0, s5, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 96(a1)
	or t0, s4, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 88(a1)
	or t0, s3, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 80(a1)
	or t0, s2, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 72(a1)
	or t0, s1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 64(a1)
	or t0, s0, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 392(a5)
	addi t1, s7, 0
	ld t3, 112(a1)
	and t0, s6, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 104(a1)
	and t0, s5, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 96(a1)
	and t0, s4, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 88(a1)
	and t0, s3, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 80(a1)
	and t0, s2, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 72(a1)
	and t0, s1, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 64(a1)
	and t0, s0, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 120(a1)
	and t0, t1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	sd s0, 576(a5)
	sd s1, 584(a5)
	sd s2, 592(a5)
	sd s3, 600(a5)
	sd s4, 608(a5)
	sd s5, 616(a5)
	sd s6, 624(a5)
	sd s7, 632(a5)
	ld s0, 512(a5)
	ld s1, 520(a5)
	ld s2, 528(a5)
	ld s3, 536(a5)
	ld s4, 544(a5)
	ld s5, 552(a5)
	ld s6, 560(a5)
	ld s7, 568(a5)
	ld t2, 392(a5)
	addi t1, s7, 0
	ld t3, 48(a1)
	and t0, s6, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 40(a1)
	and t0, s5, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 32(a1)
	and t0, s4, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 24(a1)
	and t0, s3, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 16(a1)
	and t0, s2, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 8(a1)
	and t0, s1, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 0(a1)
	and t0, s0, t3
	srli t4, t0, 56
	slli t0, t0, 8
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 56(a1)
	and t0, t1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	ld t2, 384(a5)
	ld t3, 56(a1)
	or t0, s7, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s7, s7, t0
	ld t3, 48(a1)
	or t0, s6, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s6, s6, t0
	ld t3, 40(a1)
	or t0, s5, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s5, s5, t0
	ld t3, 32(a1)
	or t0, s4, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s4, s4, t0
	ld t3, 24(a1)
	or t0, s3, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s3, s3, t0
	ld t3, 16(a1)
	or t0, s2, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s2, s2, t0
	ld t3, 8(a1)
	or t0, s1, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s1, s1, t0
	ld t3, 0(a1)
	or t0, s0, t3
	srli t4, t0, 8
	slli t0, t0, 56
	xor t0, t0, t4
	and t0, t0, t2
	xor s0, s0, t0
	sd s0, 512(a5)
	sd s1, 520(a5)
	sd s2, 528(a5)
	sd s3, 536(a5)
	sd s4, 544(a5)
	sd s5, 552(a5)
	sd s6, 560(a5)
	sd s7, 568(a5)
	addi a1, a1, 128
212:
	sub t0, a1, a4
	bnez t0, 29b
	ld t0, 64(a1)
	xor s0, s0, t0
	ld t0, 72(a1)
	xor s1, s1, t0
	ld t0, 80(a1)
	xor s2, s2, t0
	ld t0, 88(a1)
	xor s3, s3, t0
	ld t0, 96(a1)
	xor s4, s4, t0
	ld t0, 104(a1)
	xor s5, s5, t0
	ld t0, 112(a1)
	xor s6, s6, t0
	ld t0, 120(a1)
	xor s7, s7, t0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 776(a5)
	sd s1, 792(a5)
	sd s2, 808(a5)
	sd s3, 824(a5)
	sd s4, 840(a5)
	sd s5, 856(a5)
	sd s6, 872(a5)
	sd s7, 888(a5)
	ld s0, 576(a5)
	ld s1, 584(a5)
	ld s2, 592(a5)
	ld s3, 600(a5)
	ld s4, 608(a5)
	ld s5, 616(a5)
	ld s6, 624(a5)
	ld s7, 632(a5)
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t3, 424(a5)
	ld t4, 432(a5)
	ld t6, 448(a5)
	ld a6, 456(a5)
	ld a7, 464(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	sd s0, 768(a5)
	sd s1, 784(a5)
	sd s2, 800(a5)
	sd s3, 816(a5)
	sd s4, 832(a5)
	sd s5, 848(a5)
	sd s6, 864(a5)
	sd s7, 880(a5)
	srli t0, a3, 3
	bnez t0, 213f
	addi t6, a3, 0
	j 214f
213:
	addi t6, zero, 8
214:
	addi t3, a5, 768
	addi t4, a2, 0
	addi t5, t6, 0
215:
	ld t0, 0(t3)
	sb t0, 0(t4)
	srli t1, t0, 8
	sb t1, 1(t4)
	srli t1, t0, 16
	sb t1, 2(t4)
	srli t1, t0, 24
	sb t1, 3(t4)
	srli t1, t0, 32
	sb t1, 4(t4)
	srli t2, t1, 8
	sb t2, 5(t4)
	srli t2, t1, 16
	sb t2, 6(t4)
	srli t2, t1, 24
	sb t2, 7(t4)
	ld t0, 8(t3)
	sb t0, 8(t4)
	srli t1, t0, 8
	sb t1, 9(t4)
	srli t1, t0, 16
	sb t1, 10(t4)
	srli t1, t0, 24
	sb t1, 11(t4)
	srli t1, t0, 32
	sb t1, 12(t4)
	srli t2, t1, 8
	sb t2, 13(t4)
	srli t2, t1, 16
	sb t2, 14(t4)
	srli t2, t1, 24
	sb t2, 15(t4)
	addi t3, t3, 16
	addi t4, t4, 16
	addi t5, t5, -1
	bnez t5, 215b
	sub a3, a3, t6
	addi a2, a2, 128
	bnez a3, 25b
	j 24f
23:
24:
	ld s0, 640(a5)
	ld s1, 648(a5)
	ld s2, 656(a5)
	ld s3, 664(a5)
	ld s4, 672(a5)
	ld s5, 680(a5)
	ld s6, 688(a5)
	ld s7, 696(a5)
	ld s8, 704(a5)
	ld s9, 712(a5)
	ld s10, 720(a5)
	ld s11, 728(a5)
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	sd t6, 1152(t5)
	sd t6, 1160(t5)
	sd t6, 1168(t5)
	sd t6, 1176(t5)
	sd t6, 1184(t5)
	sd t6, 1192(t5)
	sd t6, 1200(t5)
	sd t6, 1208(t5)
	sd t6, 1216(t5)
	sd t6, 1224(t5)
	sd t6, 1232(t5)
	sd t6, 1240(t5)
	sd t6, 1248(t5)
	sd t6, 1256(t5)
	sd t6, 1264(t5)
	sd t6, 1272(t5)
	sd t6, 1280(t5)
	sd t6, 1288(t5)
	sd t6, 1296(t5)
	sd t6, 1304(t5)
	sd t6, 1312(t5)
	sd t6, 1320(t5)
	sd t6, 1328(t5)
	sd t6, 1336(t5)
	sd t6, 1344(t5)
	sd t6, 1352(t5)
	sd t6, 1360(t5)
	sd t6, 1368(t5)
	sd t6, 1376(t5)
	sd t6, 1384(t5)
	sd t6, 1392(t5)
	sd t6, 1400(t5)
	sd t6, 1408(t5)
	sd t6, 1416(t5)
	sd t6, 1424(t5)
	sd t6, 1432(t5)
	sd t6, 1440(t5)
	sd t6, 1448(t5)
	sd t6, 1456(t5)
	sd t6, 1464(t5)
	sd t6, 1472(t5)
	sd t6, 1480(t5)
	sd t6, 1488(t5)
	sd t6, 1496(t5)
	sd t6, 1504(t5)
	sd t6, 1512(t5)
	sd t6, 1520(t5)
	sd t6, 1528(t5)
	sd t6, 1536(t5)
	sd t6, 1544(t5)
	sd t6, 1552(t5)
	sd t6, 1560(t5)
	sd t6, 1568(t5)
	sd t6, 1576(t5)
	sd t6, 1584(t5)
	sd t6, 1592(t5)
	sd t6, 1600(t5)
	sd t6, 1608(t5)
	sd t6, 1616(t5)
	sd t6, 1624(t5)
	sd t6, 1632(t5)
	sd t6, 1640(t5)
	sd t6, 1648(t5)
	sd t6, 1656(t5)
	sd t6, 1664(t5)
	sd t6, 1672(t5)
	sd t6, 1680(t5)
	sd t6, 1688(t5)
	sd t6, 1696(t5)
	sd t6, 1704(t5)
	sd t6, 1712(t5)
	sd t6, 1720(t5)
	sd t6, 1728(t5)
	sd t6, 1736(t5)
	sd t6, 1744(t5)
	sd t6, 1752(t5)
	sd t6, 1760(t5)
	sd t6, 1768(t5)
	sd t6, 1776(t5)
	sd t6, 1784(t5)
	sd t6, 1792(t5)
	sd t6, 1800(t5)
	sd t6, 1808(t5)
	sd t6, 1816(t5)
	sd t6, 1824(t5)
	sd t6, 1832(t5)
	sd t6, 1840(t5)
	sd t6, 1848(t5)
	sd t6, 1856(t5)
	sd t6, 1864(t5)
	sd t6, 1872(t5)
	sd t6, 1880(t5)
	sd t6, 1888(t5)
	sd t6, 1896(t5)
	sd t6, 1904(t5)
	sd t6, 1912(t5)
	sd t6, 1920(t5)
	sd t6, 1928(t5)
	sd t6, 1936(t5)
	sd t6, 1944(t5)
	sd t6, 1952(t5)
	sd t6, 1960(t5)
	sd t6, 1968(t5)
	sd t6, 1976(t5)
	sd t6, 1984(t5)
	sd t6, 1992(t5)
	sd t6, 2000(t5)
	sd t6, 2008(t5)
	sd t6, 2016(t5)
	sd t6, 2024(t5)
	sd t6, 2032(t5)
	sd t6, 2040(t5)
	addi t5, t5, 1024
	addi t5, t5, 1024
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	sd t6, 576(t5)
	sd t6, 584(t5)
	sd t6, 592(t5)
	sd t6, 600(t5)
	sd t6, 608(t5)
	sd t6, 616(t5)
	sd t6, 624(t5)
	sd t6, 632(t5)
	sd t6, 640(t5)
	sd t6, 648(t5)
	sd t6, 656(t5)
	sd t6, 664(t5)
	sd t6, 672(t5)
	sd t6, 680(t5)
	sd t6, 688(t5)
	sd t6, 696(t5)
	sd t6, 704(t5)
	sd t6, 712(t5)
	sd t6, 720(t5)
	sd t6, 728(t5)
	sd t6, 736(t5)
	sd t6, 744(t5)
	sd t6, 752(t5)
	sd t6, 760(t5)
	sd t6, 768(t5)
	sd t6, 776(t5)
	sd t6, 784(t5)
	sd t6, 792(t5)
	sd t6, 800(t5)
	sd t6, 808(t5)
	sd t6, 816(t5)
	sd t6, 824(t5)
	sd t6, 832(t5)
	sd t6, 840(t5)
	sd t6, 848(t5)
	sd t6, 856(t5)
	sd t6, 864(t5)
	sd t6, 872(t5)
	sd t6, 880(t5)
	sd t6, 888(t5)
	sd t6, 896(t5)
	sd t6, 904(t5)
	sd t6, 912(t5)
	sd t6, 920(t5)
	sd t6, 928(t5)
	sd t6, 936(t5)
	sd t6, 944(t5)
	sd t6, 952(t5)
	sd t6, 960(t5)
	sd t6, 968(t5)
	sd t6, 976(t5)
	sd t6, 984(t5)
	sd t6, 992(t5)
	sd t6, 1000(t5)
	sd t6, 1008(t5)
	sd t6, 1016(t5)
	sd t6, 1024(t5)
	sd t6, 1032(t5)
	sd t6, 1040(t5)
	sd t6, 1048(t5)
	sd t6, 1056(t5)
	sd t6, 1064(t5)
	sd t6, 1072(t5)
	sd t6, 1080(t5)
	sd t6, 1088(t5)
	sd t6, 1096(t5)
	sd t6, 1104(t5)
	sd t6, 1112(t5)
	sd t6, 1120(t5)
	sd t6, 1128(t5)
	sd t6, 1136(t5)
	sd t6, 1144(t5)
	addi sp, sp, 1168
	addi sp, sp, 2032
	ret
	.option pop
