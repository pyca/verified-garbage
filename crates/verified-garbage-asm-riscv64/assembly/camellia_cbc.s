// The functions of `src/camellia_cbc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_cbc_encrypt_chained:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -18
	beqz t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi s2, a2, 0
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a1, zero, 24
	addi a5, t0, 0
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
	beqz t0, 22f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi t1, zero, 34
	j 23f
22:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi t1, zero, 26
23:
	addi a1, a5, 1024
24:
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
	bnez t1, 24b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	beqz s3, 25f
27:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1536
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
28:
	addi a0, a1, 384
29:
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
	bnez t0, 29b
	sub t0, a1, a4
	bnez t0, 210f
	j 211f
210:
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
211:
	sub t0, a1, a4
	bnez t0, 28b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 27b
	j 26f
25:
26:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 406
212:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 212b
	addi sp, sp, 1216
	addi sp, sp, 2032
	j 21f
20:
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi s2, a2, 0
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a1, zero, 18
	addi a5, t0, 0
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
	beqz t0, 213f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi t1, zero, 34
	j 214f
213:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi t1, zero, 26
214:
	addi a1, a5, 1024
215:
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
	bnez t1, 215b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	beqz s3, 216f
218:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1024
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
219:
	addi a0, a1, 384
220:
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
	bnez t0, 220b
	sub t0, a1, a4
	bnez t0, 221f
	j 222f
221:
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
222:
	sub t0, a1, a4
	bnez t0, 219b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 218b
	j 217f
216:
217:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 406
223:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 223b
	addi sp, sp, 1216
	addi sp, sp, 2032
21:
	ret
	.option pop

vg_camellia_cbc_decrypt_chained:
	.option push
	.option arch, +m, +c
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, a3, 0
	addi a3, a4, 0
	addi t0, t0, -18
	beqz t0, 20f
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi s2, a2, 0
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a1, zero, 24
	addi a5, t0, 0
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
	beqz t0, 22f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi a0, a0, 256
	addi t1, zero, 30
	j 23f
22:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi a0, a0, 192
	addi t1, zero, 22
23:
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
24:
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
	bnez t1, 24b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	srli t0, s3, 3
	beqz t0, 25f
27:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 832(s4)
	srli t2, t0, 8
	sb t2, 833(s4)
	srli t2, t0, 16
	sb t2, 834(s4)
	srli t2, t0, 24
	sb t2, 835(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 836(s4)
	srli t2, t0, 8
	sb t2, 837(s4)
	srli t2, t0, 16
	sb t2, 838(s4)
	srli t2, t0, 24
	sb t2, 839(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 840(s4)
	srli t2, t0, 8
	sb t2, 841(s4)
	srli t2, t0, 16
	sb t2, 842(s4)
	srli t2, t0, 24
	sb t2, 843(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 844(s4)
	srli t2, t0, 8
	sb t2, 845(s4)
	srli t2, t0, 16
	sb t2, 846(s4)
	srli t2, t0, 24
	sb t2, 847(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 848(s4)
	srli t2, t0, 8
	sb t2, 849(s4)
	srli t2, t0, 16
	sb t2, 850(s4)
	srli t2, t0, 24
	sb t2, 851(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 852(s4)
	srli t2, t0, 8
	sb t2, 853(s4)
	srli t2, t0, 16
	sb t2, 854(s4)
	srli t2, t0, 24
	sb t2, 855(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 856(s4)
	srli t2, t0, 8
	sb t2, 857(s4)
	srli t2, t0, 16
	sb t2, 858(s4)
	srli t2, t0, 24
	sb t2, 859(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 860(s4)
	srli t2, t0, 8
	sb t2, 861(s4)
	srli t2, t0, 16
	sb t2, 862(s4)
	srli t2, t0, 24
	sb t2, 863(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 864(s4)
	srli t2, t0, 8
	sb t2, 865(s4)
	srli t2, t0, 16
	sb t2, 866(s4)
	srli t2, t0, 24
	sb t2, 867(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 868(s4)
	srli t2, t0, 8
	sb t2, 869(s4)
	srli t2, t0, 16
	sb t2, 870(s4)
	srli t2, t0, 24
	sb t2, 871(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 872(s4)
	srli t2, t0, 8
	sb t2, 873(s4)
	srli t2, t0, 16
	sb t2, 874(s4)
	srli t2, t0, 24
	sb t2, 875(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 876(s4)
	srli t2, t0, 8
	sb t2, 877(s4)
	srli t2, t0, 16
	sb t2, 878(s4)
	srli t2, t0, 24
	sb t2, 879(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 880(s4)
	srli t2, t0, 8
	sb t2, 881(s4)
	srli t2, t0, 16
	sb t2, 882(s4)
	srli t2, t0, 24
	sb t2, 883(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 884(s4)
	srli t2, t0, 8
	sb t2, 885(s4)
	srli t2, t0, 16
	sb t2, 886(s4)
	srli t2, t0, 24
	sb t2, 887(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 888(s4)
	srli t2, t0, 8
	sb t2, 889(s4)
	srli t2, t0, 16
	sb t2, 890(s4)
	srli t2, t0, 24
	sb t2, 891(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 892(s4)
	srli t2, t0, 8
	sb t2, 893(s4)
	srli t2, t0, 16
	sb t2, 894(s4)
	srli t2, t0, 24
	sb t2, 895(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 896(s4)
	srli t2, t0, 8
	sb t2, 897(s4)
	srli t2, t0, 16
	sb t2, 898(s4)
	srli t2, t0, 24
	sb t2, 899(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 900(s4)
	srli t2, t0, 8
	sb t2, 901(s4)
	srli t2, t0, 16
	sb t2, 902(s4)
	srli t2, t0, 24
	sb t2, 903(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 904(s4)
	srli t2, t0, 8
	sb t2, 905(s4)
	srli t2, t0, 16
	sb t2, 906(s4)
	srli t2, t0, 24
	sb t2, 907(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 908(s4)
	srli t2, t0, 8
	sb t2, 909(s4)
	srli t2, t0, 16
	sb t2, 910(s4)
	srli t2, t0, 24
	sb t2, 911(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 912(s4)
	srli t2, t0, 8
	sb t2, 913(s4)
	srli t2, t0, 16
	sb t2, 914(s4)
	srli t2, t0, 24
	sb t2, 915(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 916(s4)
	srli t2, t0, 8
	sb t2, 917(s4)
	srli t2, t0, 16
	sb t2, 918(s4)
	srli t2, t0, 24
	sb t2, 919(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 920(s4)
	srli t2, t0, 8
	sb t2, 921(s4)
	srli t2, t0, 16
	sb t2, 922(s4)
	srli t2, t0, 24
	sb t2, 923(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 924(s4)
	srli t2, t0, 8
	sb t2, 925(s4)
	srli t2, t0, 16
	sb t2, 926(s4)
	srli t2, t0, 24
	sb t2, 927(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 928(s4)
	srli t2, t0, 8
	sb t2, 929(s4)
	srli t2, t0, 16
	sb t2, 930(s4)
	srli t2, t0, 24
	sb t2, 931(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 932(s4)
	srli t2, t0, 8
	sb t2, 933(s4)
	srli t2, t0, 16
	sb t2, 934(s4)
	srli t2, t0, 24
	sb t2, 935(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 936(s4)
	srli t2, t0, 8
	sb t2, 937(s4)
	srli t2, t0, 16
	sb t2, 938(s4)
	srli t2, t0, 24
	sb t2, 939(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 940(s4)
	srli t2, t0, 8
	sb t2, 941(s4)
	srli t2, t0, 16
	sb t2, 942(s4)
	srli t2, t0, 24
	sb t2, 943(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1536
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
28:
	addi a0, a1, 384
29:
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
	bnez t0, 29b
	sub t0, a1, a4
	bnez t0, 210f
	j 211f
210:
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
211:
	sub t0, a1, a4
	bnez t0, 28b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 832(s4)
	srli t2, t0, 8
	sb t2, 833(s4)
	srli t2, t0, 16
	sb t2, 834(s4)
	srli t2, t0, 24
	sb t2, 835(s4)
	lbu t0, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 836(s4)
	srli t2, t0, 8
	sb t2, 837(s4)
	srli t2, t0, 16
	sb t2, 838(s4)
	srli t2, t0, 24
	sb t2, 839(s4)
	lbu t0, 840(s4)
	lbu t2, 841(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 842(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 843(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 840(s4)
	srli t2, t0, 8
	sb t2, 841(s4)
	srli t2, t0, 16
	sb t2, 842(s4)
	srli t2, t0, 24
	sb t2, 843(s4)
	lbu t0, 844(s4)
	lbu t2, 845(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 846(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 847(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 844(s4)
	srli t2, t0, 8
	sb t2, 845(s4)
	srli t2, t0, 16
	sb t2, 846(s4)
	srli t2, t0, 24
	sb t2, 847(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 840(s4)
	lbu t2, 841(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 842(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 843(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 844(s4)
	lbu t2, 845(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 846(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 847(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 848(s4)
	lbu t2, 849(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 850(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 851(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 848(s4)
	srli t2, t0, 8
	sb t2, 849(s4)
	srli t2, t0, 16
	sb t2, 850(s4)
	srli t2, t0, 24
	sb t2, 851(s4)
	lbu t0, 852(s4)
	lbu t2, 853(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 854(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 855(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 852(s4)
	srli t2, t0, 8
	sb t2, 853(s4)
	srli t2, t0, 16
	sb t2, 854(s4)
	srli t2, t0, 24
	sb t2, 855(s4)
	lbu t0, 856(s4)
	lbu t2, 857(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 858(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 859(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 856(s4)
	srli t2, t0, 8
	sb t2, 857(s4)
	srli t2, t0, 16
	sb t2, 858(s4)
	srli t2, t0, 24
	sb t2, 859(s4)
	lbu t0, 860(s4)
	lbu t2, 861(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 862(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 863(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 860(s4)
	srli t2, t0, 8
	sb t2, 861(s4)
	srli t2, t0, 16
	sb t2, 862(s4)
	srli t2, t0, 24
	sb t2, 863(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 848(s4)
	lbu t2, 849(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 850(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 851(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 852(s4)
	lbu t2, 853(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 854(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 855(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 856(s4)
	lbu t2, 857(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 858(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 859(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 860(s4)
	lbu t2, 861(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 862(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 863(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 864(s4)
	lbu t2, 865(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 866(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 867(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 864(s4)
	srli t2, t0, 8
	sb t2, 865(s4)
	srli t2, t0, 16
	sb t2, 866(s4)
	srli t2, t0, 24
	sb t2, 867(s4)
	lbu t0, 868(s4)
	lbu t2, 869(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 870(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 871(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 868(s4)
	srli t2, t0, 8
	sb t2, 869(s4)
	srli t2, t0, 16
	sb t2, 870(s4)
	srli t2, t0, 24
	sb t2, 871(s4)
	lbu t0, 872(s4)
	lbu t2, 873(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 874(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 875(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 872(s4)
	srli t2, t0, 8
	sb t2, 873(s4)
	srli t2, t0, 16
	sb t2, 874(s4)
	srli t2, t0, 24
	sb t2, 875(s4)
	lbu t0, 876(s4)
	lbu t2, 877(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 878(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 879(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 876(s4)
	srli t2, t0, 8
	sb t2, 877(s4)
	srli t2, t0, 16
	sb t2, 878(s4)
	srli t2, t0, 24
	sb t2, 879(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 864(s4)
	lbu t2, 865(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 866(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 867(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 868(s4)
	lbu t2, 869(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 870(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 871(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 872(s4)
	lbu t2, 873(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 874(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 875(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 876(s4)
	lbu t2, 877(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 878(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 879(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 880(s4)
	lbu t2, 881(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 882(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 883(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 880(s4)
	srli t2, t0, 8
	sb t2, 881(s4)
	srli t2, t0, 16
	sb t2, 882(s4)
	srli t2, t0, 24
	sb t2, 883(s4)
	lbu t0, 884(s4)
	lbu t2, 885(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 886(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 887(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 884(s4)
	srli t2, t0, 8
	sb t2, 885(s4)
	srli t2, t0, 16
	sb t2, 886(s4)
	srli t2, t0, 24
	sb t2, 887(s4)
	lbu t0, 888(s4)
	lbu t2, 889(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 890(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 891(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 888(s4)
	srli t2, t0, 8
	sb t2, 889(s4)
	srli t2, t0, 16
	sb t2, 890(s4)
	srli t2, t0, 24
	sb t2, 891(s4)
	lbu t0, 892(s4)
	lbu t2, 893(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 894(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 895(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 892(s4)
	srli t2, t0, 8
	sb t2, 893(s4)
	srli t2, t0, 16
	sb t2, 894(s4)
	srli t2, t0, 24
	sb t2, 895(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 880(s4)
	lbu t2, 881(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 882(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 883(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 884(s4)
	lbu t2, 885(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 886(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 887(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 888(s4)
	lbu t2, 889(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 890(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 891(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 892(s4)
	lbu t2, 893(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 894(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 895(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 896(s4)
	lbu t2, 897(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 898(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 899(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 896(s4)
	srli t2, t0, 8
	sb t2, 897(s4)
	srli t2, t0, 16
	sb t2, 898(s4)
	srli t2, t0, 24
	sb t2, 899(s4)
	lbu t0, 900(s4)
	lbu t2, 901(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 902(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 903(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 900(s4)
	srli t2, t0, 8
	sb t2, 901(s4)
	srli t2, t0, 16
	sb t2, 902(s4)
	srli t2, t0, 24
	sb t2, 903(s4)
	lbu t0, 904(s4)
	lbu t2, 905(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 906(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 907(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 904(s4)
	srli t2, t0, 8
	sb t2, 905(s4)
	srli t2, t0, 16
	sb t2, 906(s4)
	srli t2, t0, 24
	sb t2, 907(s4)
	lbu t0, 908(s4)
	lbu t2, 909(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 910(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 911(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 908(s4)
	srli t2, t0, 8
	sb t2, 909(s4)
	srli t2, t0, 16
	sb t2, 910(s4)
	srli t2, t0, 24
	sb t2, 911(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 896(s4)
	lbu t2, 897(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 898(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 899(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 900(s4)
	lbu t2, 901(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 902(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 903(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 904(s4)
	lbu t2, 905(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 906(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 907(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 908(s4)
	lbu t2, 909(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 910(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 911(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 912(s4)
	lbu t2, 913(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 914(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 915(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 912(s4)
	srli t2, t0, 8
	sb t2, 913(s4)
	srli t2, t0, 16
	sb t2, 914(s4)
	srli t2, t0, 24
	sb t2, 915(s4)
	lbu t0, 916(s4)
	lbu t2, 917(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 918(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 919(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 916(s4)
	srli t2, t0, 8
	sb t2, 917(s4)
	srli t2, t0, 16
	sb t2, 918(s4)
	srli t2, t0, 24
	sb t2, 919(s4)
	lbu t0, 920(s4)
	lbu t2, 921(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 922(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 923(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 920(s4)
	srli t2, t0, 8
	sb t2, 921(s4)
	srli t2, t0, 16
	sb t2, 922(s4)
	srli t2, t0, 24
	sb t2, 923(s4)
	lbu t0, 924(s4)
	lbu t2, 925(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 926(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 927(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 924(s4)
	srli t2, t0, 8
	sb t2, 925(s4)
	srli t2, t0, 16
	sb t2, 926(s4)
	srli t2, t0, 24
	sb t2, 927(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 912(s4)
	lbu t2, 913(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 914(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 915(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 916(s4)
	lbu t2, 917(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 918(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 919(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 920(s4)
	lbu t2, 921(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 922(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 923(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 924(s4)
	lbu t2, 925(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 926(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 927(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 928(s4)
	lbu t2, 929(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 930(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 931(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 928(s4)
	srli t2, t0, 8
	sb t2, 929(s4)
	srli t2, t0, 16
	sb t2, 930(s4)
	srli t2, t0, 24
	sb t2, 931(s4)
	lbu t0, 932(s4)
	lbu t2, 933(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 934(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 935(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 932(s4)
	srli t2, t0, 8
	sb t2, 933(s4)
	srli t2, t0, 16
	sb t2, 934(s4)
	srli t2, t0, 24
	sb t2, 935(s4)
	lbu t0, 936(s4)
	lbu t2, 937(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 938(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 939(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 936(s4)
	srli t2, t0, 8
	sb t2, 937(s4)
	srli t2, t0, 16
	sb t2, 938(s4)
	srli t2, t0, 24
	sb t2, 939(s4)
	lbu t0, 940(s4)
	lbu t2, 941(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 942(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 943(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 940(s4)
	srli t2, t0, 8
	sb t2, 941(s4)
	srli t2, t0, 16
	sb t2, 942(s4)
	srli t2, t0, 24
	sb t2, 943(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 928(s4)
	lbu t2, 929(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 930(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 931(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 932(s4)
	lbu t2, 933(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 934(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 935(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 936(s4)
	lbu t2, 937(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 938(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 939(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 940(s4)
	lbu t2, 941(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 942(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 943(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 27b
	j 26f
25:
26:
	beqz s3, 212f
214:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1536
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
215:
	addi a0, a1, 384
216:
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
	bnez t0, 216b
	sub t0, a1, a4
	bnez t0, 217f
	j 218f
217:
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
218:
	sub t0, a1, a4
	bnez t0, 215b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 214b
	j 213f
212:
213:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 406
219:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 219b
	addi sp, sp, 1216
	addi sp, sp, 2032
	j 21f
20:
	addi sp, sp, -2032
	addi sp, sp, -1216
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi s2, a2, 0
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a1, zero, 18
	addi a5, t0, 0
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
	beqz t0, 220f
	addi a4, a5, 1536
	addi a4, a4, 1536
	addi a0, a0, 256
	addi t1, zero, 30
	j 221f
220:
	addi a4, a5, 1536
	addi a4, a4, 1024
	addi a0, a0, 192
	addi t1, zero, 22
221:
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
222:
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
	bnez t1, 222b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	srli t0, s3, 3
	beqz t0, 223f
225:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 832(s4)
	srli t2, t0, 8
	sb t2, 833(s4)
	srli t2, t0, 16
	sb t2, 834(s4)
	srli t2, t0, 24
	sb t2, 835(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 836(s4)
	srli t2, t0, 8
	sb t2, 837(s4)
	srli t2, t0, 16
	sb t2, 838(s4)
	srli t2, t0, 24
	sb t2, 839(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 840(s4)
	srli t2, t0, 8
	sb t2, 841(s4)
	srli t2, t0, 16
	sb t2, 842(s4)
	srli t2, t0, 24
	sb t2, 843(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 844(s4)
	srli t2, t0, 8
	sb t2, 845(s4)
	srli t2, t0, 16
	sb t2, 846(s4)
	srli t2, t0, 24
	sb t2, 847(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 848(s4)
	srli t2, t0, 8
	sb t2, 849(s4)
	srli t2, t0, 16
	sb t2, 850(s4)
	srli t2, t0, 24
	sb t2, 851(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 852(s4)
	srli t2, t0, 8
	sb t2, 853(s4)
	srli t2, t0, 16
	sb t2, 854(s4)
	srli t2, t0, 24
	sb t2, 855(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 856(s4)
	srli t2, t0, 8
	sb t2, 857(s4)
	srli t2, t0, 16
	sb t2, 858(s4)
	srli t2, t0, 24
	sb t2, 859(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 860(s4)
	srli t2, t0, 8
	sb t2, 861(s4)
	srli t2, t0, 16
	sb t2, 862(s4)
	srli t2, t0, 24
	sb t2, 863(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 864(s4)
	srli t2, t0, 8
	sb t2, 865(s4)
	srli t2, t0, 16
	sb t2, 866(s4)
	srli t2, t0, 24
	sb t2, 867(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 868(s4)
	srli t2, t0, 8
	sb t2, 869(s4)
	srli t2, t0, 16
	sb t2, 870(s4)
	srli t2, t0, 24
	sb t2, 871(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 872(s4)
	srli t2, t0, 8
	sb t2, 873(s4)
	srli t2, t0, 16
	sb t2, 874(s4)
	srli t2, t0, 24
	sb t2, 875(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 876(s4)
	srli t2, t0, 8
	sb t2, 877(s4)
	srli t2, t0, 16
	sb t2, 878(s4)
	srli t2, t0, 24
	sb t2, 879(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 880(s4)
	srli t2, t0, 8
	sb t2, 881(s4)
	srli t2, t0, 16
	sb t2, 882(s4)
	srli t2, t0, 24
	sb t2, 883(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 884(s4)
	srli t2, t0, 8
	sb t2, 885(s4)
	srli t2, t0, 16
	sb t2, 886(s4)
	srli t2, t0, 24
	sb t2, 887(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 888(s4)
	srli t2, t0, 8
	sb t2, 889(s4)
	srli t2, t0, 16
	sb t2, 890(s4)
	srli t2, t0, 24
	sb t2, 891(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 892(s4)
	srli t2, t0, 8
	sb t2, 893(s4)
	srli t2, t0, 16
	sb t2, 894(s4)
	srli t2, t0, 24
	sb t2, 895(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 896(s4)
	srli t2, t0, 8
	sb t2, 897(s4)
	srli t2, t0, 16
	sb t2, 898(s4)
	srli t2, t0, 24
	sb t2, 899(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 900(s4)
	srli t2, t0, 8
	sb t2, 901(s4)
	srli t2, t0, 16
	sb t2, 902(s4)
	srli t2, t0, 24
	sb t2, 903(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 904(s4)
	srli t2, t0, 8
	sb t2, 905(s4)
	srli t2, t0, 16
	sb t2, 906(s4)
	srli t2, t0, 24
	sb t2, 907(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 908(s4)
	srli t2, t0, 8
	sb t2, 909(s4)
	srli t2, t0, 16
	sb t2, 910(s4)
	srli t2, t0, 24
	sb t2, 911(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 912(s4)
	srli t2, t0, 8
	sb t2, 913(s4)
	srli t2, t0, 16
	sb t2, 914(s4)
	srli t2, t0, 24
	sb t2, 915(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 916(s4)
	srli t2, t0, 8
	sb t2, 917(s4)
	srli t2, t0, 16
	sb t2, 918(s4)
	srli t2, t0, 24
	sb t2, 919(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 920(s4)
	srli t2, t0, 8
	sb t2, 921(s4)
	srli t2, t0, 16
	sb t2, 922(s4)
	srli t2, t0, 24
	sb t2, 923(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 924(s4)
	srli t2, t0, 8
	sb t2, 925(s4)
	srli t2, t0, 16
	sb t2, 926(s4)
	srli t2, t0, 24
	sb t2, 927(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 928(s4)
	srli t2, t0, 8
	sb t2, 929(s4)
	srli t2, t0, 16
	sb t2, 930(s4)
	srli t2, t0, 24
	sb t2, 931(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 932(s4)
	srli t2, t0, 8
	sb t2, 933(s4)
	srli t2, t0, 16
	sb t2, 934(s4)
	srli t2, t0, 24
	sb t2, 935(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 936(s4)
	srli t2, t0, 8
	sb t2, 937(s4)
	srli t2, t0, 16
	sb t2, 938(s4)
	srli t2, t0, 24
	sb t2, 939(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 940(s4)
	srli t2, t0, 8
	sb t2, 941(s4)
	srli t2, t0, 16
	sb t2, 942(s4)
	srli t2, t0, 24
	sb t2, 943(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1024
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
226:
	addi a0, a1, 384
227:
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
	bnez t0, 227b
	sub t0, a1, a4
	bnez t0, 228f
	j 229f
228:
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
229:
	sub t0, a1, a4
	bnez t0, 226b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	lbu t0, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 832(s4)
	srli t2, t0, 8
	sb t2, 833(s4)
	srli t2, t0, 16
	sb t2, 834(s4)
	srli t2, t0, 24
	sb t2, 835(s4)
	lbu t0, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 836(s4)
	srli t2, t0, 8
	sb t2, 837(s4)
	srli t2, t0, 16
	sb t2, 838(s4)
	srli t2, t0, 24
	sb t2, 839(s4)
	lbu t0, 840(s4)
	lbu t2, 841(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 842(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 843(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 840(s4)
	srli t2, t0, 8
	sb t2, 841(s4)
	srli t2, t0, 16
	sb t2, 842(s4)
	srli t2, t0, 24
	sb t2, 843(s4)
	lbu t0, 844(s4)
	lbu t2, 845(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 846(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 847(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 844(s4)
	srli t2, t0, 8
	sb t2, 845(s4)
	srli t2, t0, 16
	sb t2, 846(s4)
	srli t2, t0, 24
	sb t2, 847(s4)
	lbu t0, 16(s2)
	lbu t2, 17(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 18(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 19(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 20(s2)
	lbu t2, 21(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 22(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 23(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 24(s2)
	lbu t2, 25(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 26(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 27(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 28(s2)
	lbu t2, 29(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 30(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 31(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 832(s4)
	lbu t2, 833(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 834(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 835(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
	lbu t0, 836(s4)
	lbu t2, 837(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 838(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 839(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
	lbu t0, 840(s4)
	lbu t2, 841(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 842(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 843(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
	lbu t0, 844(s4)
	lbu t2, 845(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 846(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 847(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
	lbu t0, 848(s4)
	lbu t2, 849(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 850(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 851(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 848(s4)
	srli t2, t0, 8
	sb t2, 849(s4)
	srli t2, t0, 16
	sb t2, 850(s4)
	srli t2, t0, 24
	sb t2, 851(s4)
	lbu t0, 852(s4)
	lbu t2, 853(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 854(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 855(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 852(s4)
	srli t2, t0, 8
	sb t2, 853(s4)
	srli t2, t0, 16
	sb t2, 854(s4)
	srli t2, t0, 24
	sb t2, 855(s4)
	lbu t0, 856(s4)
	lbu t2, 857(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 858(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 859(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 856(s4)
	srli t2, t0, 8
	sb t2, 857(s4)
	srli t2, t0, 16
	sb t2, 858(s4)
	srli t2, t0, 24
	sb t2, 859(s4)
	lbu t0, 860(s4)
	lbu t2, 861(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 862(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 863(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 860(s4)
	srli t2, t0, 8
	sb t2, 861(s4)
	srli t2, t0, 16
	sb t2, 862(s4)
	srli t2, t0, 24
	sb t2, 863(s4)
	lbu t0, 32(s2)
	lbu t2, 33(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 36(s2)
	lbu t2, 37(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 40(s2)
	lbu t2, 41(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 44(s2)
	lbu t2, 45(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 848(s4)
	lbu t2, 849(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 850(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 851(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
	lbu t0, 852(s4)
	lbu t2, 853(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 854(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 855(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
	lbu t0, 856(s4)
	lbu t2, 857(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 858(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 859(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
	lbu t0, 860(s4)
	lbu t2, 861(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 862(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 863(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
	lbu t0, 864(s4)
	lbu t2, 865(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 866(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 867(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 864(s4)
	srli t2, t0, 8
	sb t2, 865(s4)
	srli t2, t0, 16
	sb t2, 866(s4)
	srli t2, t0, 24
	sb t2, 867(s4)
	lbu t0, 868(s4)
	lbu t2, 869(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 870(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 871(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 868(s4)
	srli t2, t0, 8
	sb t2, 869(s4)
	srli t2, t0, 16
	sb t2, 870(s4)
	srli t2, t0, 24
	sb t2, 871(s4)
	lbu t0, 872(s4)
	lbu t2, 873(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 874(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 875(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 872(s4)
	srli t2, t0, 8
	sb t2, 873(s4)
	srli t2, t0, 16
	sb t2, 874(s4)
	srli t2, t0, 24
	sb t2, 875(s4)
	lbu t0, 876(s4)
	lbu t2, 877(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 878(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 879(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 876(s4)
	srli t2, t0, 8
	sb t2, 877(s4)
	srli t2, t0, 16
	sb t2, 878(s4)
	srli t2, t0, 24
	sb t2, 879(s4)
	lbu t0, 48(s2)
	lbu t2, 49(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 50(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 51(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 52(s2)
	lbu t2, 53(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 54(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 55(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 56(s2)
	lbu t2, 57(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 58(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 59(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 60(s2)
	lbu t2, 61(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 62(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 63(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 864(s4)
	lbu t2, 865(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 866(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 867(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
	lbu t0, 868(s4)
	lbu t2, 869(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 870(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 871(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
	lbu t0, 872(s4)
	lbu t2, 873(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 874(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 875(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
	lbu t0, 876(s4)
	lbu t2, 877(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 878(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 879(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
	lbu t0, 880(s4)
	lbu t2, 881(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 882(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 883(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 880(s4)
	srli t2, t0, 8
	sb t2, 881(s4)
	srli t2, t0, 16
	sb t2, 882(s4)
	srli t2, t0, 24
	sb t2, 883(s4)
	lbu t0, 884(s4)
	lbu t2, 885(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 886(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 887(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 884(s4)
	srli t2, t0, 8
	sb t2, 885(s4)
	srli t2, t0, 16
	sb t2, 886(s4)
	srli t2, t0, 24
	sb t2, 887(s4)
	lbu t0, 888(s4)
	lbu t2, 889(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 890(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 891(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 888(s4)
	srli t2, t0, 8
	sb t2, 889(s4)
	srli t2, t0, 16
	sb t2, 890(s4)
	srli t2, t0, 24
	sb t2, 891(s4)
	lbu t0, 892(s4)
	lbu t2, 893(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 894(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 895(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 892(s4)
	srli t2, t0, 8
	sb t2, 893(s4)
	srli t2, t0, 16
	sb t2, 894(s4)
	srli t2, t0, 24
	sb t2, 895(s4)
	lbu t0, 64(s2)
	lbu t2, 65(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 66(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 67(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 68(s2)
	lbu t2, 69(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 70(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 71(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 72(s2)
	lbu t2, 73(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 74(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 75(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 76(s2)
	lbu t2, 77(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 78(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 79(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 880(s4)
	lbu t2, 881(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 882(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 883(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
	lbu t0, 884(s4)
	lbu t2, 885(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 886(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 887(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
	lbu t0, 888(s4)
	lbu t2, 889(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 890(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 891(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
	lbu t0, 892(s4)
	lbu t2, 893(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 894(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 895(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
	lbu t0, 896(s4)
	lbu t2, 897(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 898(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 899(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 896(s4)
	srli t2, t0, 8
	sb t2, 897(s4)
	srli t2, t0, 16
	sb t2, 898(s4)
	srli t2, t0, 24
	sb t2, 899(s4)
	lbu t0, 900(s4)
	lbu t2, 901(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 902(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 903(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 900(s4)
	srli t2, t0, 8
	sb t2, 901(s4)
	srli t2, t0, 16
	sb t2, 902(s4)
	srli t2, t0, 24
	sb t2, 903(s4)
	lbu t0, 904(s4)
	lbu t2, 905(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 906(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 907(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 904(s4)
	srli t2, t0, 8
	sb t2, 905(s4)
	srli t2, t0, 16
	sb t2, 906(s4)
	srli t2, t0, 24
	sb t2, 907(s4)
	lbu t0, 908(s4)
	lbu t2, 909(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 910(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 911(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 908(s4)
	srli t2, t0, 8
	sb t2, 909(s4)
	srli t2, t0, 16
	sb t2, 910(s4)
	srli t2, t0, 24
	sb t2, 911(s4)
	lbu t0, 80(s2)
	lbu t2, 81(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 82(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 83(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 84(s2)
	lbu t2, 85(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 86(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 87(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 88(s2)
	lbu t2, 89(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 90(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 91(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 92(s2)
	lbu t2, 93(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 94(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 95(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 896(s4)
	lbu t2, 897(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 898(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 899(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
	lbu t0, 900(s4)
	lbu t2, 901(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 902(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 903(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
	lbu t0, 904(s4)
	lbu t2, 905(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 906(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 907(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
	lbu t0, 908(s4)
	lbu t2, 909(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 910(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 911(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
	lbu t0, 912(s4)
	lbu t2, 913(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 914(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 915(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 912(s4)
	srli t2, t0, 8
	sb t2, 913(s4)
	srli t2, t0, 16
	sb t2, 914(s4)
	srli t2, t0, 24
	sb t2, 915(s4)
	lbu t0, 916(s4)
	lbu t2, 917(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 918(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 919(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 916(s4)
	srli t2, t0, 8
	sb t2, 917(s4)
	srli t2, t0, 16
	sb t2, 918(s4)
	srli t2, t0, 24
	sb t2, 919(s4)
	lbu t0, 920(s4)
	lbu t2, 921(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 922(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 923(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 920(s4)
	srli t2, t0, 8
	sb t2, 921(s4)
	srli t2, t0, 16
	sb t2, 922(s4)
	srli t2, t0, 24
	sb t2, 923(s4)
	lbu t0, 924(s4)
	lbu t2, 925(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 926(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 927(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 924(s4)
	srli t2, t0, 8
	sb t2, 925(s4)
	srli t2, t0, 16
	sb t2, 926(s4)
	srli t2, t0, 24
	sb t2, 927(s4)
	lbu t0, 96(s2)
	lbu t2, 97(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 98(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 99(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 100(s2)
	lbu t2, 101(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 102(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 103(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 104(s2)
	lbu t2, 105(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 106(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 107(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 108(s2)
	lbu t2, 109(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 110(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 111(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 912(s4)
	lbu t2, 913(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 914(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 915(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
	lbu t0, 916(s4)
	lbu t2, 917(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 918(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 919(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
	lbu t0, 920(s4)
	lbu t2, 921(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 922(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 923(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
	lbu t0, 924(s4)
	lbu t2, 925(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 926(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 927(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
	lbu t0, 928(s4)
	lbu t2, 929(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 930(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 931(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 928(s4)
	srli t2, t0, 8
	sb t2, 929(s4)
	srli t2, t0, 16
	sb t2, 930(s4)
	srli t2, t0, 24
	sb t2, 931(s4)
	lbu t0, 932(s4)
	lbu t2, 933(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 934(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 935(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 932(s4)
	srli t2, t0, 8
	sb t2, 933(s4)
	srli t2, t0, 16
	sb t2, 934(s4)
	srli t2, t0, 24
	sb t2, 935(s4)
	lbu t0, 936(s4)
	lbu t2, 937(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 938(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 939(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 936(s4)
	srli t2, t0, 8
	sb t2, 937(s4)
	srli t2, t0, 16
	sb t2, 938(s4)
	srli t2, t0, 24
	sb t2, 939(s4)
	lbu t0, 940(s4)
	lbu t2, 941(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 942(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 943(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 940(s4)
	srli t2, t0, 8
	sb t2, 941(s4)
	srli t2, t0, 16
	sb t2, 942(s4)
	srli t2, t0, 24
	sb t2, 943(s4)
	lbu t0, 112(s2)
	lbu t2, 113(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 114(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 115(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 116(s2)
	lbu t2, 117(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 118(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 119(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 120(s2)
	lbu t2, 121(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 122(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 123(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 124(s2)
	lbu t2, 125(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 126(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 127(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 928(s4)
	lbu t2, 929(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 930(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 931(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
	lbu t0, 932(s4)
	lbu t2, 933(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 934(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 935(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
	lbu t0, 936(s4)
	lbu t2, 937(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 938(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 939(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
	lbu t0, 940(s4)
	lbu t2, 941(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 942(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 943(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	addi s2, s2, 128
	addi s3, s3, -8
	srli t0, s3, 3
	bnez t0, 225b
	j 224f
223:
224:
	beqz s3, 230f
232:
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	addi t0, s4, 48
	sd ra, 784(s4)
	sd a0, 792(s4)
	addi a2, s1, 0
	addi a3, s2, 0
	addi ra, s3, 0
	addi a5, t0, 0
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
	addi a4, a5, 1536
	addi a4, a4, 1024
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
233:
	addi a0, a1, 384
234:
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
	bnez t0, 234b
	sub t0, a1, a4
	bnez t0, 235f
	j 236f
235:
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
236:
	sub t0, a1, a4
	bnez t0, 233b
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
	addi s1, a2, 0
	addi s2, a3, 0
	addi s3, ra, 0
	addi s4, a5, -48
	ld ra, 736(a5)
	ld a0, 744(a5)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 816(s4)
	srli t2, t0, 8
	sb t2, 817(s4)
	srli t2, t0, 16
	sb t2, 818(s4)
	srli t2, t0, 24
	sb t2, 819(s4)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 820(s4)
	srli t2, t0, 8
	sb t2, 821(s4)
	srli t2, t0, 16
	sb t2, 822(s4)
	srli t2, t0, 24
	sb t2, 823(s4)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 824(s4)
	srli t2, t0, 8
	sb t2, 825(s4)
	srli t2, t0, 16
	sb t2, 826(s4)
	srli t2, t0, 24
	sb t2, 827(s4)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 828(s4)
	srli t2, t0, 8
	sb t2, 829(s4)
	srli t2, t0, 16
	sb t2, 830(s4)
	srli t2, t0, 24
	sb t2, 831(s4)
	lbu t0, 0(s2)
	lbu t2, 1(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 2(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 3(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 4(s2)
	lbu t2, 5(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 6(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 7(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 8(s2)
	lbu t2, 9(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 10(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 11(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 12(s2)
	lbu t2, 13(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 14(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 15(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	lbu t0, 816(s4)
	lbu t2, 817(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 818(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 819(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 820(s4)
	lbu t2, 821(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 822(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 823(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 824(s4)
	lbu t2, 825(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 826(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 827(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 828(s4)
	lbu t2, 829(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 830(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 831(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 232b
	j 231f
230:
231:
	addi s2, s1, 0
	lbu t0, 32(s4)
	lbu t2, 33(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 34(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 35(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
	lbu t0, 36(s4)
	lbu t2, 37(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 38(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 39(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
	lbu t0, 40(s4)
	lbu t2, 41(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 42(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 43(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
	lbu t0, 44(s4)
	lbu t2, 45(s4)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 46(s4)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 47(s4)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 406
237:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 237b
	addi sp, sp, 1216
	addi sp, sp, 2032
21:
	ret
	.option pop
