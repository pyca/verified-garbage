// The functions of `src/seed_cfb.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cfb128_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1104
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
	beqz s3, 20f
22:
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
	sb t0, 1080(s4)
	srli t2, t0, 8
	sb t2, 1081(s4)
	srli t2, t0, 16
	sb t2, 1082(s4)
	srli t2, t0, 24
	sb t2, 1083(s4)
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
	sb t0, 1084(s4)
	srli t2, t0, 8
	sb t2, 1085(s4)
	srli t2, t0, 16
	sb t2, 1086(s4)
	srli t2, t0, 24
	sb t2, 1087(s4)
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
	sb t0, 1088(s4)
	srli t2, t0, 8
	sb t2, 1089(s4)
	srli t2, t0, 16
	sb t2, 1090(s4)
	srli t2, t0, 24
	sb t2, 1091(s4)
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
	sb t0, 1092(s4)
	srli t2, t0, 8
	sb t2, 1093(s4)
	srli t2, t0, 16
	sb t2, 1094(s4)
	srli t2, t0, 24
	sb t2, 1095(s4)
	addi t0, s4, 48
	addi a5, t0, 0
	sd s0, 936(a5)
	sd s1, 944(a5)
	sd s2, 952(a5)
	sd s3, 960(a5)
	sd s4, 968(a5)
	sd s5, 976(a5)
	sd s6, 984(a5)
	sd s7, 992(a5)
	sd s8, 1000(a5)
	sd s9, 1008(a5)
	sd s10, 1016(a5)
	sd s11, 1024(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 832(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 840(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 848(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 856(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 864(a5)
	lui t0, 851917
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 851917
	addiw t1, t1, -4
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 872(a5)
	lui t0, 3892
	addiw t0, t0, -13
	slli t0, t0, 32
	lui t1, 3892
	addiw t1, t1, -13
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 880(a5)
	lui t0, 258048
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 258048
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 888(a5)
	lui t0, 16
	addiw t0, t0, -817
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -817
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 896(a5)
	lui t0, 1035504
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1035504
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 904(a5)
	lui t0, 0
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 63
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 912(a5)
	lui t0, 996351
	addiw t0, t0, 768
	slli t0, t0, 32
	lui t1, 996351
	addiw t1, t1, 768
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 920(a5)
	lui t0, 946878
	addiw t0, t0, 1835
	slli t0, t0, 32
	lui t1, 946878
	addiw t1, t1, 1835
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 928(a5)
	addi a3, a5, 832
	sd ra, 1048(a5)
	addi a1, s1, 0
	addi a2, s2, 0
	addi ra, s3, 0
	addi a0, a0, 0
	addi t2, zero, 1
	addi t3, a5, 1032
	addi t4, a5, 0
23:
	lbu t0, 0(t3)
	slli t0, t0, 24
	lbu t1, 1(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 2(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 3(t3)
	or t0, t0, t1
	sw t0, 576(t4)
	lbu t0, 4(t3)
	slli t0, t0, 24
	lbu t1, 5(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 6(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 7(t3)
	or t0, t0, t1
	sw t0, 640(t4)
	lbu t0, 8(t3)
	slli t0, t0, 24
	lbu t1, 9(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 10(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 11(t3)
	or t0, t0, t1
	sw t0, 704(t4)
	lbu t0, 12(t3)
	slli t0, t0, 24
	lbu t1, 13(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 14(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 15(t3)
	or t0, t0, t1
	sw t0, 768(t4)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 23b
	addi a4, zero, 16
24:
	lbu t5, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or t5, t5, t0
	lbu t6, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t6, t6, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t6, t6, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t6, t6, t0
	lwu t0, 704(a5)
	xor t0, t0, t5
	sw t0, 384(a5)
	lwu t1, 768(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 320(a5)
	lwu t0, 708(a5)
	xor t0, t0, t5
	sw t0, 388(a5)
	lwu t1, 772(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 324(a5)
	lwu t0, 712(a5)
	xor t0, t0, t5
	sw t0, 392(a5)
	lwu t1, 776(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 328(a5)
	lwu t0, 716(a5)
	xor t0, t0, t5
	sw t0, 396(a5)
	lwu t1, 780(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 332(a5)
	lwu t0, 720(a5)
	xor t0, t0, t5
	sw t0, 400(a5)
	lwu t1, 784(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 336(a5)
	lwu t0, 724(a5)
	xor t0, t0, t5
	sw t0, 404(a5)
	lwu t1, 788(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 340(a5)
	lwu t0, 728(a5)
	xor t0, t0, t5
	sw t0, 408(a5)
	lwu t1, 792(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 344(a5)
	lwu t0, 732(a5)
	xor t0, t0, t5
	sw t0, 412(a5)
	lwu t1, 796(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 348(a5)
	lwu t0, 736(a5)
	xor t0, t0, t5
	sw t0, 416(a5)
	lwu t1, 800(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 352(a5)
	lwu t0, 740(a5)
	xor t0, t0, t5
	sw t0, 420(a5)
	lwu t1, 804(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 356(a5)
	lwu t0, 744(a5)
	xor t0, t0, t5
	sw t0, 424(a5)
	lwu t1, 808(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 360(a5)
	lwu t0, 748(a5)
	xor t0, t0, t5
	sw t0, 428(a5)
	lwu t1, 812(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 364(a5)
	lwu t0, 752(a5)
	xor t0, t0, t5
	sw t0, 432(a5)
	lwu t1, 816(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 368(a5)
	lwu t0, 756(a5)
	xor t0, t0, t5
	sw t0, 436(a5)
	lwu t1, 820(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 372(a5)
	lwu t0, 760(a5)
	xor t0, t0, t5
	sw t0, 440(a5)
	lwu t1, 824(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 376(a5)
	lwu t0, 764(a5)
	xor t0, t0, t5
	sw t0, 444(a5)
	lwu t1, 828(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 448(a5)
	lwu t1, 384(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 452(a5)
	lwu t1, 388(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 456(a5)
	lwu t1, 392(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 460(a5)
	lwu t1, 396(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 464(a5)
	lwu t1, 400(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 468(a5)
	lwu t1, 404(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 472(a5)
	lwu t1, 408(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 476(a5)
	lwu t1, 412(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 480(a5)
	lwu t1, 416(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 484(a5)
	lwu t1, 420(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 488(a5)
	lwu t1, 424(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 492(a5)
	lwu t1, 428(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 496(a5)
	lwu t1, 432(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 500(a5)
	lwu t1, 436(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 504(a5)
	lwu t1, 440(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 508(a5)
	lwu t1, 444(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 512(a5)
	lwu t1, 448(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 516(a5)
	lwu t1, 452(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 520(a5)
	lwu t1, 456(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 524(a5)
	lwu t1, 460(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 528(a5)
	lwu t1, 464(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 532(a5)
	lwu t1, 468(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 536(a5)
	lwu t1, 472(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 540(a5)
	lwu t1, 476(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 544(a5)
	lwu t1, 480(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 548(a5)
	lwu t1, 484(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 552(a5)
	lwu t1, 488(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 556(a5)
	lwu t1, 492(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 560(a5)
	lwu t1, 496(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 564(a5)
	lwu t1, 500(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 568(a5)
	lwu t1, 504(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 572(a5)
	lwu t1, 508(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	lwu t1, 640(a5)
	xor t1, t1, t0
	sw t1, 640(a5)
	lwu t1, 512(a5)
	add t0, t0, t1
	lwu t1, 576(a5)
	xor t0, t0, t1
	sw t0, 576(a5)
	lwu t0, 324(a5)
	lwu t1, 644(a5)
	xor t1, t1, t0
	sw t1, 644(a5)
	lwu t1, 516(a5)
	add t0, t0, t1
	lwu t1, 580(a5)
	xor t0, t0, t1
	sw t0, 580(a5)
	lwu t0, 328(a5)
	lwu t1, 648(a5)
	xor t1, t1, t0
	sw t1, 648(a5)
	lwu t1, 520(a5)
	add t0, t0, t1
	lwu t1, 584(a5)
	xor t0, t0, t1
	sw t0, 584(a5)
	lwu t0, 332(a5)
	lwu t1, 652(a5)
	xor t1, t1, t0
	sw t1, 652(a5)
	lwu t1, 524(a5)
	add t0, t0, t1
	lwu t1, 588(a5)
	xor t0, t0, t1
	sw t0, 588(a5)
	lwu t0, 336(a5)
	lwu t1, 656(a5)
	xor t1, t1, t0
	sw t1, 656(a5)
	lwu t1, 528(a5)
	add t0, t0, t1
	lwu t1, 592(a5)
	xor t0, t0, t1
	sw t0, 592(a5)
	lwu t0, 340(a5)
	lwu t1, 660(a5)
	xor t1, t1, t0
	sw t1, 660(a5)
	lwu t1, 532(a5)
	add t0, t0, t1
	lwu t1, 596(a5)
	xor t0, t0, t1
	sw t0, 596(a5)
	lwu t0, 344(a5)
	lwu t1, 664(a5)
	xor t1, t1, t0
	sw t1, 664(a5)
	lwu t1, 536(a5)
	add t0, t0, t1
	lwu t1, 600(a5)
	xor t0, t0, t1
	sw t0, 600(a5)
	lwu t0, 348(a5)
	lwu t1, 668(a5)
	xor t1, t1, t0
	sw t1, 668(a5)
	lwu t1, 540(a5)
	add t0, t0, t1
	lwu t1, 604(a5)
	xor t0, t0, t1
	sw t0, 604(a5)
	lwu t0, 352(a5)
	lwu t1, 672(a5)
	xor t1, t1, t0
	sw t1, 672(a5)
	lwu t1, 544(a5)
	add t0, t0, t1
	lwu t1, 608(a5)
	xor t0, t0, t1
	sw t0, 608(a5)
	lwu t0, 356(a5)
	lwu t1, 676(a5)
	xor t1, t1, t0
	sw t1, 676(a5)
	lwu t1, 548(a5)
	add t0, t0, t1
	lwu t1, 612(a5)
	xor t0, t0, t1
	sw t0, 612(a5)
	lwu t0, 360(a5)
	lwu t1, 680(a5)
	xor t1, t1, t0
	sw t1, 680(a5)
	lwu t1, 552(a5)
	add t0, t0, t1
	lwu t1, 616(a5)
	xor t0, t0, t1
	sw t0, 616(a5)
	lwu t0, 364(a5)
	lwu t1, 684(a5)
	xor t1, t1, t0
	sw t1, 684(a5)
	lwu t1, 556(a5)
	add t0, t0, t1
	lwu t1, 620(a5)
	xor t0, t0, t1
	sw t0, 620(a5)
	lwu t0, 368(a5)
	lwu t1, 688(a5)
	xor t1, t1, t0
	sw t1, 688(a5)
	lwu t1, 560(a5)
	add t0, t0, t1
	lwu t1, 624(a5)
	xor t0, t0, t1
	sw t0, 624(a5)
	lwu t0, 372(a5)
	lwu t1, 692(a5)
	xor t1, t1, t0
	sw t1, 692(a5)
	lwu t1, 564(a5)
	add t0, t0, t1
	lwu t1, 628(a5)
	xor t0, t0, t1
	sw t0, 628(a5)
	lwu t0, 376(a5)
	lwu t1, 696(a5)
	xor t1, t1, t0
	sw t1, 696(a5)
	lwu t1, 568(a5)
	add t0, t0, t1
	lwu t1, 632(a5)
	xor t0, t0, t1
	sw t0, 632(a5)
	lwu t0, 380(a5)
	lwu t1, 700(a5)
	xor t1, t1, t0
	sw t1, 700(a5)
	lwu t1, 572(a5)
	add t0, t0, t1
	lwu t1, 636(a5)
	xor t0, t0, t1
	sw t0, 636(a5)
	ld t0, 576(a5)
	ld t1, 704(a5)
	sd t1, 576(a5)
	sd t0, 704(a5)
	ld t0, 584(a5)
	ld t1, 712(a5)
	sd t1, 584(a5)
	sd t0, 712(a5)
	ld t0, 592(a5)
	ld t1, 720(a5)
	sd t1, 592(a5)
	sd t0, 720(a5)
	ld t0, 600(a5)
	ld t1, 728(a5)
	sd t1, 600(a5)
	sd t0, 728(a5)
	ld t0, 608(a5)
	ld t1, 736(a5)
	sd t1, 608(a5)
	sd t0, 736(a5)
	ld t0, 616(a5)
	ld t1, 744(a5)
	sd t1, 616(a5)
	sd t0, 744(a5)
	ld t0, 624(a5)
	ld t1, 752(a5)
	sd t1, 624(a5)
	sd t0, 752(a5)
	ld t0, 632(a5)
	ld t1, 760(a5)
	sd t1, 632(a5)
	sd t0, 760(a5)
	ld t0, 640(a5)
	ld t1, 768(a5)
	sd t1, 640(a5)
	sd t0, 768(a5)
	ld t0, 648(a5)
	ld t1, 776(a5)
	sd t1, 648(a5)
	sd t0, 776(a5)
	ld t0, 656(a5)
	ld t1, 784(a5)
	sd t1, 656(a5)
	sd t0, 784(a5)
	ld t0, 664(a5)
	ld t1, 792(a5)
	sd t1, 664(a5)
	sd t0, 792(a5)
	ld t0, 672(a5)
	ld t1, 800(a5)
	sd t1, 672(a5)
	sd t0, 800(a5)
	ld t0, 680(a5)
	ld t1, 808(a5)
	sd t1, 680(a5)
	sd t0, 808(a5)
	ld t0, 688(a5)
	ld t1, 816(a5)
	sd t1, 688(a5)
	sd t0, 816(a5)
	ld t0, 696(a5)
	ld t1, 824(a5)
	sd t1, 696(a5)
	sd t0, 824(a5)
	addi a0, a0, 8
	addi a4, a4, -1
	bnez a4, 24b
	addi a0, a0, -128
	addi t2, zero, 1
	addi t3, a5, 1032
	addi t4, a5, 0
25:
	lwu t0, 704(t4)
	srli t1, t0, 24
	sb t1, 0(t3)
	srli t1, t0, 16
	sb t1, 1(t3)
	srli t1, t0, 8
	sb t1, 2(t3)
	srli t1, t0, 0
	sb t1, 3(t3)
	lwu t0, 768(t4)
	srli t1, t0, 24
	sb t1, 4(t3)
	srli t1, t0, 16
	sb t1, 5(t3)
	srli t1, t0, 8
	sb t1, 6(t3)
	srli t1, t0, 0
	sb t1, 7(t3)
	lwu t0, 576(t4)
	srli t1, t0, 24
	sb t1, 8(t3)
	srli t1, t0, 16
	sb t1, 9(t3)
	srli t1, t0, 8
	sb t1, 10(t3)
	srli t1, t0, 0
	sb t1, 11(t3)
	lwu t0, 640(t4)
	srli t1, t0, 24
	sb t1, 12(t3)
	srli t1, t0, 16
	sb t1, 13(t3)
	srli t1, t0, 8
	sb t1, 14(t3)
	srli t1, t0, 0
	sb t1, 15(t3)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 25b
	addi a0, a0, 0
	ld s0, 936(a5)
	ld s1, 944(a5)
	ld s2, 952(a5)
	ld s3, 960(a5)
	ld s4, 968(a5)
	ld s5, 976(a5)
	ld s6, 984(a5)
	ld s7, 992(a5)
	ld s8, 1000(a5)
	ld s9, 1008(a5)
	ld s10, 1016(a5)
	ld s11, 1024(a5)
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, ra, 0
	ld ra, 1048(a5)
	addi s4, a5, -48
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
	lbu t1, 1080(s4)
	lbu t2, 1081(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1082(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1083(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
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
	lbu t1, 1084(s4)
	lbu t2, 1085(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1086(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1087(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
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
	lbu t1, 1088(s4)
	lbu t2, 1089(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1090(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1091(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
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
	lbu t1, 1092(s4)
	lbu t2, 1093(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1094(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1095(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
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
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 22b
	j 21f
20:
21:
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
	addi t2, zero, 138
26:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 26b
	addi sp, sp, 1104
	ret
	.option pop

vg_seed_cfb128_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1344
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
	srli t0, s3, 4
	beqz t0, 20f
22:
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
	sb t0, 1080(s4)
	srli t2, t0, 8
	sb t2, 1081(s4)
	srli t2, t0, 16
	sb t2, 1082(s4)
	srli t2, t0, 24
	sb t2, 1083(s4)
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
	sb t0, 1084(s4)
	srli t2, t0, 8
	sb t2, 1085(s4)
	srli t2, t0, 16
	sb t2, 1086(s4)
	srli t2, t0, 24
	sb t2, 1087(s4)
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
	sb t0, 1088(s4)
	srli t2, t0, 8
	sb t2, 1089(s4)
	srli t2, t0, 16
	sb t2, 1090(s4)
	srli t2, t0, 24
	sb t2, 1091(s4)
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
	sb t0, 1092(s4)
	srli t2, t0, 8
	sb t2, 1093(s4)
	srli t2, t0, 16
	sb t2, 1094(s4)
	srli t2, t0, 24
	sb t2, 1095(s4)
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
	sb t0, 1096(s4)
	srli t2, t0, 8
	sb t2, 1097(s4)
	srli t2, t0, 16
	sb t2, 1098(s4)
	srli t2, t0, 24
	sb t2, 1099(s4)
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
	sb t0, 1100(s4)
	srli t2, t0, 8
	sb t2, 1101(s4)
	srli t2, t0, 16
	sb t2, 1102(s4)
	srli t2, t0, 24
	sb t2, 1103(s4)
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
	sb t0, 1104(s4)
	srli t2, t0, 8
	sb t2, 1105(s4)
	srli t2, t0, 16
	sb t2, 1106(s4)
	srli t2, t0, 24
	sb t2, 1107(s4)
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
	sb t0, 1108(s4)
	srli t2, t0, 8
	sb t2, 1109(s4)
	srli t2, t0, 16
	sb t2, 1110(s4)
	srli t2, t0, 24
	sb t2, 1111(s4)
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
	sb t0, 1112(s4)
	srli t2, t0, 8
	sb t2, 1113(s4)
	srli t2, t0, 16
	sb t2, 1114(s4)
	srli t2, t0, 24
	sb t2, 1115(s4)
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
	sb t0, 1116(s4)
	srli t2, t0, 8
	sb t2, 1117(s4)
	srli t2, t0, 16
	sb t2, 1118(s4)
	srli t2, t0, 24
	sb t2, 1119(s4)
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
	sb t0, 1120(s4)
	srli t2, t0, 8
	sb t2, 1121(s4)
	srli t2, t0, 16
	sb t2, 1122(s4)
	srli t2, t0, 24
	sb t2, 1123(s4)
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
	sb t0, 1124(s4)
	srli t2, t0, 8
	sb t2, 1125(s4)
	srli t2, t0, 16
	sb t2, 1126(s4)
	srli t2, t0, 24
	sb t2, 1127(s4)
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
	sb t0, 1128(s4)
	srli t2, t0, 8
	sb t2, 1129(s4)
	srli t2, t0, 16
	sb t2, 1130(s4)
	srli t2, t0, 24
	sb t2, 1131(s4)
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
	sb t0, 1132(s4)
	srli t2, t0, 8
	sb t2, 1133(s4)
	srli t2, t0, 16
	sb t2, 1134(s4)
	srli t2, t0, 24
	sb t2, 1135(s4)
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
	sb t0, 1136(s4)
	srli t2, t0, 8
	sb t2, 1137(s4)
	srli t2, t0, 16
	sb t2, 1138(s4)
	srli t2, t0, 24
	sb t2, 1139(s4)
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
	sb t0, 1140(s4)
	srli t2, t0, 8
	sb t2, 1141(s4)
	srli t2, t0, 16
	sb t2, 1142(s4)
	srli t2, t0, 24
	sb t2, 1143(s4)
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
	sb t0, 1144(s4)
	srli t2, t0, 8
	sb t2, 1145(s4)
	srli t2, t0, 16
	sb t2, 1146(s4)
	srli t2, t0, 24
	sb t2, 1147(s4)
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
	sb t0, 1148(s4)
	srli t2, t0, 8
	sb t2, 1149(s4)
	srli t2, t0, 16
	sb t2, 1150(s4)
	srli t2, t0, 24
	sb t2, 1151(s4)
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
	sb t0, 1152(s4)
	srli t2, t0, 8
	sb t2, 1153(s4)
	srli t2, t0, 16
	sb t2, 1154(s4)
	srli t2, t0, 24
	sb t2, 1155(s4)
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
	sb t0, 1156(s4)
	srli t2, t0, 8
	sb t2, 1157(s4)
	srli t2, t0, 16
	sb t2, 1158(s4)
	srli t2, t0, 24
	sb t2, 1159(s4)
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
	sb t0, 1160(s4)
	srli t2, t0, 8
	sb t2, 1161(s4)
	srli t2, t0, 16
	sb t2, 1162(s4)
	srli t2, t0, 24
	sb t2, 1163(s4)
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
	sb t0, 1164(s4)
	srli t2, t0, 8
	sb t2, 1165(s4)
	srli t2, t0, 16
	sb t2, 1166(s4)
	srli t2, t0, 24
	sb t2, 1167(s4)
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
	sb t0, 1168(s4)
	srli t2, t0, 8
	sb t2, 1169(s4)
	srli t2, t0, 16
	sb t2, 1170(s4)
	srli t2, t0, 24
	sb t2, 1171(s4)
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
	sb t0, 1172(s4)
	srli t2, t0, 8
	sb t2, 1173(s4)
	srli t2, t0, 16
	sb t2, 1174(s4)
	srli t2, t0, 24
	sb t2, 1175(s4)
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
	sb t0, 1176(s4)
	srli t2, t0, 8
	sb t2, 1177(s4)
	srli t2, t0, 16
	sb t2, 1178(s4)
	srli t2, t0, 24
	sb t2, 1179(s4)
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
	sb t0, 1180(s4)
	srli t2, t0, 8
	sb t2, 1181(s4)
	srli t2, t0, 16
	sb t2, 1182(s4)
	srli t2, t0, 24
	sb t2, 1183(s4)
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
	sb t0, 1184(s4)
	srli t2, t0, 8
	sb t2, 1185(s4)
	srli t2, t0, 16
	sb t2, 1186(s4)
	srli t2, t0, 24
	sb t2, 1187(s4)
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
	sb t0, 1188(s4)
	srli t2, t0, 8
	sb t2, 1189(s4)
	srli t2, t0, 16
	sb t2, 1190(s4)
	srli t2, t0, 24
	sb t2, 1191(s4)
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
	sb t0, 1192(s4)
	srli t2, t0, 8
	sb t2, 1193(s4)
	srli t2, t0, 16
	sb t2, 1194(s4)
	srli t2, t0, 24
	sb t2, 1195(s4)
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
	sb t0, 1196(s4)
	srli t2, t0, 8
	sb t2, 1197(s4)
	srli t2, t0, 16
	sb t2, 1198(s4)
	srli t2, t0, 24
	sb t2, 1199(s4)
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
	sb t0, 1200(s4)
	srli t2, t0, 8
	sb t2, 1201(s4)
	srli t2, t0, 16
	sb t2, 1202(s4)
	srli t2, t0, 24
	sb t2, 1203(s4)
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
	sb t0, 1204(s4)
	srli t2, t0, 8
	sb t2, 1205(s4)
	srli t2, t0, 16
	sb t2, 1206(s4)
	srli t2, t0, 24
	sb t2, 1207(s4)
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
	sb t0, 1208(s4)
	srli t2, t0, 8
	sb t2, 1209(s4)
	srli t2, t0, 16
	sb t2, 1210(s4)
	srli t2, t0, 24
	sb t2, 1211(s4)
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
	sb t0, 1212(s4)
	srli t2, t0, 8
	sb t2, 1213(s4)
	srli t2, t0, 16
	sb t2, 1214(s4)
	srli t2, t0, 24
	sb t2, 1215(s4)
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
	sb t0, 1216(s4)
	srli t2, t0, 8
	sb t2, 1217(s4)
	srli t2, t0, 16
	sb t2, 1218(s4)
	srli t2, t0, 24
	sb t2, 1219(s4)
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
	sb t0, 1220(s4)
	srli t2, t0, 8
	sb t2, 1221(s4)
	srli t2, t0, 16
	sb t2, 1222(s4)
	srli t2, t0, 24
	sb t2, 1223(s4)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1224(s4)
	srli t2, t0, 8
	sb t2, 1225(s4)
	srli t2, t0, 16
	sb t2, 1226(s4)
	srli t2, t0, 24
	sb t2, 1227(s4)
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
	sb t0, 1228(s4)
	srli t2, t0, 8
	sb t2, 1229(s4)
	srli t2, t0, 16
	sb t2, 1230(s4)
	srli t2, t0, 24
	sb t2, 1231(s4)
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
	sb t0, 1232(s4)
	srli t2, t0, 8
	sb t2, 1233(s4)
	srli t2, t0, 16
	sb t2, 1234(s4)
	srli t2, t0, 24
	sb t2, 1235(s4)
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
	sb t0, 1236(s4)
	srli t2, t0, 8
	sb t2, 1237(s4)
	srli t2, t0, 16
	sb t2, 1238(s4)
	srli t2, t0, 24
	sb t2, 1239(s4)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1240(s4)
	srli t2, t0, 8
	sb t2, 1241(s4)
	srli t2, t0, 16
	sb t2, 1242(s4)
	srli t2, t0, 24
	sb t2, 1243(s4)
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
	sb t0, 1244(s4)
	srli t2, t0, 8
	sb t2, 1245(s4)
	srli t2, t0, 16
	sb t2, 1246(s4)
	srli t2, t0, 24
	sb t2, 1247(s4)
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
	sb t0, 1248(s4)
	srli t2, t0, 8
	sb t2, 1249(s4)
	srli t2, t0, 16
	sb t2, 1250(s4)
	srli t2, t0, 24
	sb t2, 1251(s4)
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
	sb t0, 1252(s4)
	srli t2, t0, 8
	sb t2, 1253(s4)
	srli t2, t0, 16
	sb t2, 1254(s4)
	srli t2, t0, 24
	sb t2, 1255(s4)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1256(s4)
	srli t2, t0, 8
	sb t2, 1257(s4)
	srli t2, t0, 16
	sb t2, 1258(s4)
	srli t2, t0, 24
	sb t2, 1259(s4)
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
	sb t0, 1260(s4)
	srli t2, t0, 8
	sb t2, 1261(s4)
	srli t2, t0, 16
	sb t2, 1262(s4)
	srli t2, t0, 24
	sb t2, 1263(s4)
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
	sb t0, 1264(s4)
	srli t2, t0, 8
	sb t2, 1265(s4)
	srli t2, t0, 16
	sb t2, 1266(s4)
	srli t2, t0, 24
	sb t2, 1267(s4)
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
	sb t0, 1268(s4)
	srli t2, t0, 8
	sb t2, 1269(s4)
	srli t2, t0, 16
	sb t2, 1270(s4)
	srli t2, t0, 24
	sb t2, 1271(s4)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1272(s4)
	srli t2, t0, 8
	sb t2, 1273(s4)
	srli t2, t0, 16
	sb t2, 1274(s4)
	srli t2, t0, 24
	sb t2, 1275(s4)
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
	sb t0, 1276(s4)
	srli t2, t0, 8
	sb t2, 1277(s4)
	srli t2, t0, 16
	sb t2, 1278(s4)
	srli t2, t0, 24
	sb t2, 1279(s4)
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
	sb t0, 1280(s4)
	srli t2, t0, 8
	sb t2, 1281(s4)
	srli t2, t0, 16
	sb t2, 1282(s4)
	srli t2, t0, 24
	sb t2, 1283(s4)
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
	sb t0, 1284(s4)
	srli t2, t0, 8
	sb t2, 1285(s4)
	srli t2, t0, 16
	sb t2, 1286(s4)
	srli t2, t0, 24
	sb t2, 1287(s4)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1288(s4)
	srli t2, t0, 8
	sb t2, 1289(s4)
	srli t2, t0, 16
	sb t2, 1290(s4)
	srli t2, t0, 24
	sb t2, 1291(s4)
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
	sb t0, 1292(s4)
	srli t2, t0, 8
	sb t2, 1293(s4)
	srli t2, t0, 16
	sb t2, 1294(s4)
	srli t2, t0, 24
	sb t2, 1295(s4)
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
	sb t0, 1296(s4)
	srli t2, t0, 8
	sb t2, 1297(s4)
	srli t2, t0, 16
	sb t2, 1298(s4)
	srli t2, t0, 24
	sb t2, 1299(s4)
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
	sb t0, 1300(s4)
	srli t2, t0, 8
	sb t2, 1301(s4)
	srli t2, t0, 16
	sb t2, 1302(s4)
	srli t2, t0, 24
	sb t2, 1303(s4)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1304(s4)
	srli t2, t0, 8
	sb t2, 1305(s4)
	srli t2, t0, 16
	sb t2, 1306(s4)
	srli t2, t0, 24
	sb t2, 1307(s4)
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
	sb t0, 1308(s4)
	srli t2, t0, 8
	sb t2, 1309(s4)
	srli t2, t0, 16
	sb t2, 1310(s4)
	srli t2, t0, 24
	sb t2, 1311(s4)
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
	sb t0, 1312(s4)
	srli t2, t0, 8
	sb t2, 1313(s4)
	srli t2, t0, 16
	sb t2, 1314(s4)
	srli t2, t0, 24
	sb t2, 1315(s4)
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
	sb t0, 1316(s4)
	srli t2, t0, 8
	sb t2, 1317(s4)
	srli t2, t0, 16
	sb t2, 1318(s4)
	srli t2, t0, 24
	sb t2, 1319(s4)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
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
	sb t0, 1320(s4)
	srli t2, t0, 8
	sb t2, 1321(s4)
	srli t2, t0, 16
	sb t2, 1322(s4)
	srli t2, t0, 24
	sb t2, 1323(s4)
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
	sb t0, 1324(s4)
	srli t2, t0, 8
	sb t2, 1325(s4)
	srli t2, t0, 16
	sb t2, 1326(s4)
	srli t2, t0, 24
	sb t2, 1327(s4)
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
	sb t0, 1328(s4)
	srli t2, t0, 8
	sb t2, 1329(s4)
	srli t2, t0, 16
	sb t2, 1330(s4)
	srli t2, t0, 24
	sb t2, 1331(s4)
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
	sb t0, 1332(s4)
	srli t2, t0, 8
	sb t2, 1333(s4)
	srli t2, t0, 16
	sb t2, 1334(s4)
	srli t2, t0, 24
	sb t2, 1335(s4)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 32(s4)
	srli t2, t0, 8
	sb t2, 33(s4)
	srli t2, t0, 16
	sb t2, 34(s4)
	srli t2, t0, 24
	sb t2, 35(s4)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 36(s4)
	srli t2, t0, 8
	sb t2, 37(s4)
	srli t2, t0, 16
	sb t2, 38(s4)
	srli t2, t0, 24
	sb t2, 39(s4)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 40(s4)
	srli t2, t0, 8
	sb t2, 41(s4)
	srli t2, t0, 16
	sb t2, 42(s4)
	srli t2, t0, 24
	sb t2, 43(s4)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	sb t0, 44(s4)
	srli t2, t0, 8
	sb t2, 45(s4)
	srli t2, t0, 16
	sb t2, 46(s4)
	srli t2, t0, 24
	sb t2, 47(s4)
	addi t0, s4, 48
	addi a5, t0, 0
	sd s0, 936(a5)
	sd s1, 944(a5)
	sd s2, 952(a5)
	sd s3, 960(a5)
	sd s4, 968(a5)
	sd s5, 976(a5)
	sd s6, 984(a5)
	sd s7, 992(a5)
	sd s8, 1000(a5)
	sd s9, 1008(a5)
	sd s10, 1016(a5)
	sd s11, 1024(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 832(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 840(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 848(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 856(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 864(a5)
	lui t0, 851917
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 851917
	addiw t1, t1, -4
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 872(a5)
	lui t0, 3892
	addiw t0, t0, -13
	slli t0, t0, 32
	lui t1, 3892
	addiw t1, t1, -13
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 880(a5)
	lui t0, 258048
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 258048
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 888(a5)
	lui t0, 16
	addiw t0, t0, -817
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -817
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 896(a5)
	lui t0, 1035504
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1035504
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 904(a5)
	lui t0, 0
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 63
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 912(a5)
	lui t0, 996351
	addiw t0, t0, 768
	slli t0, t0, 32
	lui t1, 996351
	addiw t1, t1, 768
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 920(a5)
	lui t0, 946878
	addiw t0, t0, 1835
	slli t0, t0, 32
	lui t1, 946878
	addiw t1, t1, 1835
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 928(a5)
	addi a3, a5, 832
	sd ra, 1288(a5)
	addi a1, s1, 0
	addi a2, s2, 0
	addi ra, s3, 0
	addi a0, a0, 0
	addi t2, zero, 16
	addi t3, a5, 1032
	addi t4, a5, 0
23:
	lbu t0, 0(t3)
	slli t0, t0, 24
	lbu t1, 1(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 2(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 3(t3)
	or t0, t0, t1
	sw t0, 576(t4)
	lbu t0, 4(t3)
	slli t0, t0, 24
	lbu t1, 5(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 6(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 7(t3)
	or t0, t0, t1
	sw t0, 640(t4)
	lbu t0, 8(t3)
	slli t0, t0, 24
	lbu t1, 9(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 10(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 11(t3)
	or t0, t0, t1
	sw t0, 704(t4)
	lbu t0, 12(t3)
	slli t0, t0, 24
	lbu t1, 13(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 14(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 15(t3)
	or t0, t0, t1
	sw t0, 768(t4)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 23b
	addi a4, zero, 16
24:
	lbu t5, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or t5, t5, t0
	lbu t6, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t6, t6, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t6, t6, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t6, t6, t0
	lwu t0, 704(a5)
	xor t0, t0, t5
	sw t0, 384(a5)
	lwu t1, 768(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 320(a5)
	lwu t0, 708(a5)
	xor t0, t0, t5
	sw t0, 388(a5)
	lwu t1, 772(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 324(a5)
	lwu t0, 712(a5)
	xor t0, t0, t5
	sw t0, 392(a5)
	lwu t1, 776(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 328(a5)
	lwu t0, 716(a5)
	xor t0, t0, t5
	sw t0, 396(a5)
	lwu t1, 780(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 332(a5)
	lwu t0, 720(a5)
	xor t0, t0, t5
	sw t0, 400(a5)
	lwu t1, 784(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 336(a5)
	lwu t0, 724(a5)
	xor t0, t0, t5
	sw t0, 404(a5)
	lwu t1, 788(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 340(a5)
	lwu t0, 728(a5)
	xor t0, t0, t5
	sw t0, 408(a5)
	lwu t1, 792(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 344(a5)
	lwu t0, 732(a5)
	xor t0, t0, t5
	sw t0, 412(a5)
	lwu t1, 796(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 348(a5)
	lwu t0, 736(a5)
	xor t0, t0, t5
	sw t0, 416(a5)
	lwu t1, 800(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 352(a5)
	lwu t0, 740(a5)
	xor t0, t0, t5
	sw t0, 420(a5)
	lwu t1, 804(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 356(a5)
	lwu t0, 744(a5)
	xor t0, t0, t5
	sw t0, 424(a5)
	lwu t1, 808(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 360(a5)
	lwu t0, 748(a5)
	xor t0, t0, t5
	sw t0, 428(a5)
	lwu t1, 812(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 364(a5)
	lwu t0, 752(a5)
	xor t0, t0, t5
	sw t0, 432(a5)
	lwu t1, 816(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 368(a5)
	lwu t0, 756(a5)
	xor t0, t0, t5
	sw t0, 436(a5)
	lwu t1, 820(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 372(a5)
	lwu t0, 760(a5)
	xor t0, t0, t5
	sw t0, 440(a5)
	lwu t1, 824(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 376(a5)
	lwu t0, 764(a5)
	xor t0, t0, t5
	sw t0, 444(a5)
	lwu t1, 828(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 448(a5)
	lwu t1, 384(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 452(a5)
	lwu t1, 388(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 456(a5)
	lwu t1, 392(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 460(a5)
	lwu t1, 396(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 464(a5)
	lwu t1, 400(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 468(a5)
	lwu t1, 404(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 472(a5)
	lwu t1, 408(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 476(a5)
	lwu t1, 412(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 480(a5)
	lwu t1, 416(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 484(a5)
	lwu t1, 420(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 488(a5)
	lwu t1, 424(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 492(a5)
	lwu t1, 428(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 496(a5)
	lwu t1, 432(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 500(a5)
	lwu t1, 436(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 504(a5)
	lwu t1, 440(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 508(a5)
	lwu t1, 444(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 512(a5)
	lwu t1, 448(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 516(a5)
	lwu t1, 452(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 520(a5)
	lwu t1, 456(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 524(a5)
	lwu t1, 460(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 528(a5)
	lwu t1, 464(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 532(a5)
	lwu t1, 468(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 536(a5)
	lwu t1, 472(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 540(a5)
	lwu t1, 476(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 544(a5)
	lwu t1, 480(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 548(a5)
	lwu t1, 484(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 552(a5)
	lwu t1, 488(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 556(a5)
	lwu t1, 492(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 560(a5)
	lwu t1, 496(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 564(a5)
	lwu t1, 500(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 568(a5)
	lwu t1, 504(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 572(a5)
	lwu t1, 508(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	lwu t1, 640(a5)
	xor t1, t1, t0
	sw t1, 640(a5)
	lwu t1, 512(a5)
	add t0, t0, t1
	lwu t1, 576(a5)
	xor t0, t0, t1
	sw t0, 576(a5)
	lwu t0, 324(a5)
	lwu t1, 644(a5)
	xor t1, t1, t0
	sw t1, 644(a5)
	lwu t1, 516(a5)
	add t0, t0, t1
	lwu t1, 580(a5)
	xor t0, t0, t1
	sw t0, 580(a5)
	lwu t0, 328(a5)
	lwu t1, 648(a5)
	xor t1, t1, t0
	sw t1, 648(a5)
	lwu t1, 520(a5)
	add t0, t0, t1
	lwu t1, 584(a5)
	xor t0, t0, t1
	sw t0, 584(a5)
	lwu t0, 332(a5)
	lwu t1, 652(a5)
	xor t1, t1, t0
	sw t1, 652(a5)
	lwu t1, 524(a5)
	add t0, t0, t1
	lwu t1, 588(a5)
	xor t0, t0, t1
	sw t0, 588(a5)
	lwu t0, 336(a5)
	lwu t1, 656(a5)
	xor t1, t1, t0
	sw t1, 656(a5)
	lwu t1, 528(a5)
	add t0, t0, t1
	lwu t1, 592(a5)
	xor t0, t0, t1
	sw t0, 592(a5)
	lwu t0, 340(a5)
	lwu t1, 660(a5)
	xor t1, t1, t0
	sw t1, 660(a5)
	lwu t1, 532(a5)
	add t0, t0, t1
	lwu t1, 596(a5)
	xor t0, t0, t1
	sw t0, 596(a5)
	lwu t0, 344(a5)
	lwu t1, 664(a5)
	xor t1, t1, t0
	sw t1, 664(a5)
	lwu t1, 536(a5)
	add t0, t0, t1
	lwu t1, 600(a5)
	xor t0, t0, t1
	sw t0, 600(a5)
	lwu t0, 348(a5)
	lwu t1, 668(a5)
	xor t1, t1, t0
	sw t1, 668(a5)
	lwu t1, 540(a5)
	add t0, t0, t1
	lwu t1, 604(a5)
	xor t0, t0, t1
	sw t0, 604(a5)
	lwu t0, 352(a5)
	lwu t1, 672(a5)
	xor t1, t1, t0
	sw t1, 672(a5)
	lwu t1, 544(a5)
	add t0, t0, t1
	lwu t1, 608(a5)
	xor t0, t0, t1
	sw t0, 608(a5)
	lwu t0, 356(a5)
	lwu t1, 676(a5)
	xor t1, t1, t0
	sw t1, 676(a5)
	lwu t1, 548(a5)
	add t0, t0, t1
	lwu t1, 612(a5)
	xor t0, t0, t1
	sw t0, 612(a5)
	lwu t0, 360(a5)
	lwu t1, 680(a5)
	xor t1, t1, t0
	sw t1, 680(a5)
	lwu t1, 552(a5)
	add t0, t0, t1
	lwu t1, 616(a5)
	xor t0, t0, t1
	sw t0, 616(a5)
	lwu t0, 364(a5)
	lwu t1, 684(a5)
	xor t1, t1, t0
	sw t1, 684(a5)
	lwu t1, 556(a5)
	add t0, t0, t1
	lwu t1, 620(a5)
	xor t0, t0, t1
	sw t0, 620(a5)
	lwu t0, 368(a5)
	lwu t1, 688(a5)
	xor t1, t1, t0
	sw t1, 688(a5)
	lwu t1, 560(a5)
	add t0, t0, t1
	lwu t1, 624(a5)
	xor t0, t0, t1
	sw t0, 624(a5)
	lwu t0, 372(a5)
	lwu t1, 692(a5)
	xor t1, t1, t0
	sw t1, 692(a5)
	lwu t1, 564(a5)
	add t0, t0, t1
	lwu t1, 628(a5)
	xor t0, t0, t1
	sw t0, 628(a5)
	lwu t0, 376(a5)
	lwu t1, 696(a5)
	xor t1, t1, t0
	sw t1, 696(a5)
	lwu t1, 568(a5)
	add t0, t0, t1
	lwu t1, 632(a5)
	xor t0, t0, t1
	sw t0, 632(a5)
	lwu t0, 380(a5)
	lwu t1, 700(a5)
	xor t1, t1, t0
	sw t1, 700(a5)
	lwu t1, 572(a5)
	add t0, t0, t1
	lwu t1, 636(a5)
	xor t0, t0, t1
	sw t0, 636(a5)
	ld t0, 576(a5)
	ld t1, 704(a5)
	sd t1, 576(a5)
	sd t0, 704(a5)
	ld t0, 584(a5)
	ld t1, 712(a5)
	sd t1, 584(a5)
	sd t0, 712(a5)
	ld t0, 592(a5)
	ld t1, 720(a5)
	sd t1, 592(a5)
	sd t0, 720(a5)
	ld t0, 600(a5)
	ld t1, 728(a5)
	sd t1, 600(a5)
	sd t0, 728(a5)
	ld t0, 608(a5)
	ld t1, 736(a5)
	sd t1, 608(a5)
	sd t0, 736(a5)
	ld t0, 616(a5)
	ld t1, 744(a5)
	sd t1, 616(a5)
	sd t0, 744(a5)
	ld t0, 624(a5)
	ld t1, 752(a5)
	sd t1, 624(a5)
	sd t0, 752(a5)
	ld t0, 632(a5)
	ld t1, 760(a5)
	sd t1, 632(a5)
	sd t0, 760(a5)
	ld t0, 640(a5)
	ld t1, 768(a5)
	sd t1, 640(a5)
	sd t0, 768(a5)
	ld t0, 648(a5)
	ld t1, 776(a5)
	sd t1, 648(a5)
	sd t0, 776(a5)
	ld t0, 656(a5)
	ld t1, 784(a5)
	sd t1, 656(a5)
	sd t0, 784(a5)
	ld t0, 664(a5)
	ld t1, 792(a5)
	sd t1, 664(a5)
	sd t0, 792(a5)
	ld t0, 672(a5)
	ld t1, 800(a5)
	sd t1, 672(a5)
	sd t0, 800(a5)
	ld t0, 680(a5)
	ld t1, 808(a5)
	sd t1, 680(a5)
	sd t0, 808(a5)
	ld t0, 688(a5)
	ld t1, 816(a5)
	sd t1, 688(a5)
	sd t0, 816(a5)
	ld t0, 696(a5)
	ld t1, 824(a5)
	sd t1, 696(a5)
	sd t0, 824(a5)
	addi a0, a0, 8
	addi a4, a4, -1
	bnez a4, 24b
	addi a0, a0, -128
	addi t2, zero, 16
	addi t3, a5, 1032
	addi t4, a5, 0
25:
	lwu t0, 704(t4)
	srli t1, t0, 24
	sb t1, 0(t3)
	srli t1, t0, 16
	sb t1, 1(t3)
	srli t1, t0, 8
	sb t1, 2(t3)
	srli t1, t0, 0
	sb t1, 3(t3)
	lwu t0, 768(t4)
	srli t1, t0, 24
	sb t1, 4(t3)
	srli t1, t0, 16
	sb t1, 5(t3)
	srli t1, t0, 8
	sb t1, 6(t3)
	srli t1, t0, 0
	sb t1, 7(t3)
	lwu t0, 576(t4)
	srli t1, t0, 24
	sb t1, 8(t3)
	srli t1, t0, 16
	sb t1, 9(t3)
	srli t1, t0, 8
	sb t1, 10(t3)
	srli t1, t0, 0
	sb t1, 11(t3)
	lwu t0, 640(t4)
	srli t1, t0, 24
	sb t1, 12(t3)
	srli t1, t0, 16
	sb t1, 13(t3)
	srli t1, t0, 8
	sb t1, 14(t3)
	srli t1, t0, 0
	sb t1, 15(t3)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 25b
	addi a0, a0, 0
	ld s0, 936(a5)
	ld s1, 944(a5)
	ld s2, 952(a5)
	ld s3, 960(a5)
	ld s4, 968(a5)
	ld s5, 976(a5)
	ld s6, 984(a5)
	ld s7, 992(a5)
	ld s8, 1000(a5)
	ld s9, 1008(a5)
	ld s10, 1016(a5)
	ld s11, 1024(a5)
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, ra, 0
	ld ra, 1288(a5)
	addi s4, a5, -48
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
	lbu t1, 1080(s4)
	lbu t2, 1081(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1082(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1083(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
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
	lbu t1, 1084(s4)
	lbu t2, 1085(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1086(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1087(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
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
	lbu t1, 1088(s4)
	lbu t2, 1089(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1090(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1091(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
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
	lbu t1, 1092(s4)
	lbu t2, 1093(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1094(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1095(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
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
	lbu t1, 1096(s4)
	lbu t2, 1097(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1098(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1099(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 16(s2)
	srli t2, t0, 8
	sb t2, 17(s2)
	srli t2, t0, 16
	sb t2, 18(s2)
	srli t2, t0, 24
	sb t2, 19(s2)
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
	lbu t1, 1100(s4)
	lbu t2, 1101(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1102(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1103(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 20(s2)
	srli t2, t0, 8
	sb t2, 21(s2)
	srli t2, t0, 16
	sb t2, 22(s2)
	srli t2, t0, 24
	sb t2, 23(s2)
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
	lbu t1, 1104(s4)
	lbu t2, 1105(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1106(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1107(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 24(s2)
	srli t2, t0, 8
	sb t2, 25(s2)
	srli t2, t0, 16
	sb t2, 26(s2)
	srli t2, t0, 24
	sb t2, 27(s2)
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
	lbu t1, 1108(s4)
	lbu t2, 1109(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1110(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1111(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 28(s2)
	srli t2, t0, 8
	sb t2, 29(s2)
	srli t2, t0, 16
	sb t2, 30(s2)
	srli t2, t0, 24
	sb t2, 31(s2)
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
	lbu t1, 1112(s4)
	lbu t2, 1113(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1114(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1115(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 32(s2)
	srli t2, t0, 8
	sb t2, 33(s2)
	srli t2, t0, 16
	sb t2, 34(s2)
	srli t2, t0, 24
	sb t2, 35(s2)
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
	lbu t1, 1116(s4)
	lbu t2, 1117(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1118(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1119(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 36(s2)
	srli t2, t0, 8
	sb t2, 37(s2)
	srli t2, t0, 16
	sb t2, 38(s2)
	srli t2, t0, 24
	sb t2, 39(s2)
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
	lbu t1, 1120(s4)
	lbu t2, 1121(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1122(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1123(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 40(s2)
	srli t2, t0, 8
	sb t2, 41(s2)
	srli t2, t0, 16
	sb t2, 42(s2)
	srli t2, t0, 24
	sb t2, 43(s2)
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
	lbu t1, 1124(s4)
	lbu t2, 1125(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1126(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1127(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 44(s2)
	srli t2, t0, 8
	sb t2, 45(s2)
	srli t2, t0, 16
	sb t2, 46(s2)
	srli t2, t0, 24
	sb t2, 47(s2)
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
	lbu t1, 1128(s4)
	lbu t2, 1129(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1130(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1131(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 48(s2)
	srli t2, t0, 8
	sb t2, 49(s2)
	srli t2, t0, 16
	sb t2, 50(s2)
	srli t2, t0, 24
	sb t2, 51(s2)
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
	lbu t1, 1132(s4)
	lbu t2, 1133(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1134(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1135(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 52(s2)
	srli t2, t0, 8
	sb t2, 53(s2)
	srli t2, t0, 16
	sb t2, 54(s2)
	srli t2, t0, 24
	sb t2, 55(s2)
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
	lbu t1, 1136(s4)
	lbu t2, 1137(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1138(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1139(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 56(s2)
	srli t2, t0, 8
	sb t2, 57(s2)
	srli t2, t0, 16
	sb t2, 58(s2)
	srli t2, t0, 24
	sb t2, 59(s2)
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
	lbu t1, 1140(s4)
	lbu t2, 1141(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1142(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1143(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 60(s2)
	srli t2, t0, 8
	sb t2, 61(s2)
	srli t2, t0, 16
	sb t2, 62(s2)
	srli t2, t0, 24
	sb t2, 63(s2)
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
	lbu t1, 1144(s4)
	lbu t2, 1145(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1146(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1147(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 64(s2)
	srli t2, t0, 8
	sb t2, 65(s2)
	srli t2, t0, 16
	sb t2, 66(s2)
	srli t2, t0, 24
	sb t2, 67(s2)
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
	lbu t1, 1148(s4)
	lbu t2, 1149(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1150(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1151(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 68(s2)
	srli t2, t0, 8
	sb t2, 69(s2)
	srli t2, t0, 16
	sb t2, 70(s2)
	srli t2, t0, 24
	sb t2, 71(s2)
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
	lbu t1, 1152(s4)
	lbu t2, 1153(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1154(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1155(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 72(s2)
	srli t2, t0, 8
	sb t2, 73(s2)
	srli t2, t0, 16
	sb t2, 74(s2)
	srli t2, t0, 24
	sb t2, 75(s2)
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
	lbu t1, 1156(s4)
	lbu t2, 1157(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1158(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1159(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 76(s2)
	srli t2, t0, 8
	sb t2, 77(s2)
	srli t2, t0, 16
	sb t2, 78(s2)
	srli t2, t0, 24
	sb t2, 79(s2)
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
	lbu t1, 1160(s4)
	lbu t2, 1161(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1162(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1163(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 80(s2)
	srli t2, t0, 8
	sb t2, 81(s2)
	srli t2, t0, 16
	sb t2, 82(s2)
	srli t2, t0, 24
	sb t2, 83(s2)
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
	lbu t1, 1164(s4)
	lbu t2, 1165(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1166(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1167(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 84(s2)
	srli t2, t0, 8
	sb t2, 85(s2)
	srli t2, t0, 16
	sb t2, 86(s2)
	srli t2, t0, 24
	sb t2, 87(s2)
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
	lbu t1, 1168(s4)
	lbu t2, 1169(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1170(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1171(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 88(s2)
	srli t2, t0, 8
	sb t2, 89(s2)
	srli t2, t0, 16
	sb t2, 90(s2)
	srli t2, t0, 24
	sb t2, 91(s2)
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
	lbu t1, 1172(s4)
	lbu t2, 1173(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1174(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1175(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 92(s2)
	srli t2, t0, 8
	sb t2, 93(s2)
	srli t2, t0, 16
	sb t2, 94(s2)
	srli t2, t0, 24
	sb t2, 95(s2)
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
	lbu t1, 1176(s4)
	lbu t2, 1177(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1178(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1179(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 96(s2)
	srli t2, t0, 8
	sb t2, 97(s2)
	srli t2, t0, 16
	sb t2, 98(s2)
	srli t2, t0, 24
	sb t2, 99(s2)
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
	lbu t1, 1180(s4)
	lbu t2, 1181(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1182(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1183(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 100(s2)
	srli t2, t0, 8
	sb t2, 101(s2)
	srli t2, t0, 16
	sb t2, 102(s2)
	srli t2, t0, 24
	sb t2, 103(s2)
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
	lbu t1, 1184(s4)
	lbu t2, 1185(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1186(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1187(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 104(s2)
	srli t2, t0, 8
	sb t2, 105(s2)
	srli t2, t0, 16
	sb t2, 106(s2)
	srli t2, t0, 24
	sb t2, 107(s2)
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
	lbu t1, 1188(s4)
	lbu t2, 1189(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1190(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1191(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 108(s2)
	srli t2, t0, 8
	sb t2, 109(s2)
	srli t2, t0, 16
	sb t2, 110(s2)
	srli t2, t0, 24
	sb t2, 111(s2)
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
	lbu t1, 1192(s4)
	lbu t2, 1193(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1194(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1195(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 112(s2)
	srli t2, t0, 8
	sb t2, 113(s2)
	srli t2, t0, 16
	sb t2, 114(s2)
	srli t2, t0, 24
	sb t2, 115(s2)
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
	lbu t1, 1196(s4)
	lbu t2, 1197(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1198(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1199(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 116(s2)
	srli t2, t0, 8
	sb t2, 117(s2)
	srli t2, t0, 16
	sb t2, 118(s2)
	srli t2, t0, 24
	sb t2, 119(s2)
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
	lbu t1, 1200(s4)
	lbu t2, 1201(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1202(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1203(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 120(s2)
	srli t2, t0, 8
	sb t2, 121(s2)
	srli t2, t0, 16
	sb t2, 122(s2)
	srli t2, t0, 24
	sb t2, 123(s2)
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
	lbu t1, 1204(s4)
	lbu t2, 1205(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1206(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1207(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 124(s2)
	srli t2, t0, 8
	sb t2, 125(s2)
	srli t2, t0, 16
	sb t2, 126(s2)
	srli t2, t0, 24
	sb t2, 127(s2)
	lbu t0, 128(s2)
	lbu t2, 129(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 130(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 131(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1208(s4)
	lbu t2, 1209(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1210(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1211(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 128(s2)
	srli t2, t0, 8
	sb t2, 129(s2)
	srli t2, t0, 16
	sb t2, 130(s2)
	srli t2, t0, 24
	sb t2, 131(s2)
	lbu t0, 132(s2)
	lbu t2, 133(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 134(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 135(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1212(s4)
	lbu t2, 1213(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1214(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1215(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 132(s2)
	srli t2, t0, 8
	sb t2, 133(s2)
	srli t2, t0, 16
	sb t2, 134(s2)
	srli t2, t0, 24
	sb t2, 135(s2)
	lbu t0, 136(s2)
	lbu t2, 137(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 138(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 139(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1216(s4)
	lbu t2, 1217(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1218(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1219(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 136(s2)
	srli t2, t0, 8
	sb t2, 137(s2)
	srli t2, t0, 16
	sb t2, 138(s2)
	srli t2, t0, 24
	sb t2, 139(s2)
	lbu t0, 140(s2)
	lbu t2, 141(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 142(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 143(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1220(s4)
	lbu t2, 1221(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1222(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1223(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 140(s2)
	srli t2, t0, 8
	sb t2, 141(s2)
	srli t2, t0, 16
	sb t2, 142(s2)
	srli t2, t0, 24
	sb t2, 143(s2)
	lbu t0, 144(s2)
	lbu t2, 145(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 146(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 147(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1224(s4)
	lbu t2, 1225(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1226(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1227(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 144(s2)
	srli t2, t0, 8
	sb t2, 145(s2)
	srli t2, t0, 16
	sb t2, 146(s2)
	srli t2, t0, 24
	sb t2, 147(s2)
	lbu t0, 148(s2)
	lbu t2, 149(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 150(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 151(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1228(s4)
	lbu t2, 1229(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1230(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1231(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 148(s2)
	srli t2, t0, 8
	sb t2, 149(s2)
	srli t2, t0, 16
	sb t2, 150(s2)
	srli t2, t0, 24
	sb t2, 151(s2)
	lbu t0, 152(s2)
	lbu t2, 153(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 154(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 155(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1232(s4)
	lbu t2, 1233(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1234(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1235(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 152(s2)
	srli t2, t0, 8
	sb t2, 153(s2)
	srli t2, t0, 16
	sb t2, 154(s2)
	srli t2, t0, 24
	sb t2, 155(s2)
	lbu t0, 156(s2)
	lbu t2, 157(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 158(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 159(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1236(s4)
	lbu t2, 1237(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1238(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1239(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 156(s2)
	srli t2, t0, 8
	sb t2, 157(s2)
	srli t2, t0, 16
	sb t2, 158(s2)
	srli t2, t0, 24
	sb t2, 159(s2)
	lbu t0, 160(s2)
	lbu t2, 161(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 162(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 163(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1240(s4)
	lbu t2, 1241(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1242(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1243(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 160(s2)
	srli t2, t0, 8
	sb t2, 161(s2)
	srli t2, t0, 16
	sb t2, 162(s2)
	srli t2, t0, 24
	sb t2, 163(s2)
	lbu t0, 164(s2)
	lbu t2, 165(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 166(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 167(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1244(s4)
	lbu t2, 1245(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1246(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1247(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 164(s2)
	srli t2, t0, 8
	sb t2, 165(s2)
	srli t2, t0, 16
	sb t2, 166(s2)
	srli t2, t0, 24
	sb t2, 167(s2)
	lbu t0, 168(s2)
	lbu t2, 169(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 170(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 171(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1248(s4)
	lbu t2, 1249(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1250(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1251(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 168(s2)
	srli t2, t0, 8
	sb t2, 169(s2)
	srli t2, t0, 16
	sb t2, 170(s2)
	srli t2, t0, 24
	sb t2, 171(s2)
	lbu t0, 172(s2)
	lbu t2, 173(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 174(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 175(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1252(s4)
	lbu t2, 1253(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1254(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1255(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 172(s2)
	srli t2, t0, 8
	sb t2, 173(s2)
	srli t2, t0, 16
	sb t2, 174(s2)
	srli t2, t0, 24
	sb t2, 175(s2)
	lbu t0, 176(s2)
	lbu t2, 177(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 178(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 179(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1256(s4)
	lbu t2, 1257(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1258(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1259(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 176(s2)
	srli t2, t0, 8
	sb t2, 177(s2)
	srli t2, t0, 16
	sb t2, 178(s2)
	srli t2, t0, 24
	sb t2, 179(s2)
	lbu t0, 180(s2)
	lbu t2, 181(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 182(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 183(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1260(s4)
	lbu t2, 1261(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1262(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1263(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 180(s2)
	srli t2, t0, 8
	sb t2, 181(s2)
	srli t2, t0, 16
	sb t2, 182(s2)
	srli t2, t0, 24
	sb t2, 183(s2)
	lbu t0, 184(s2)
	lbu t2, 185(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 186(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 187(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1264(s4)
	lbu t2, 1265(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1266(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1267(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 184(s2)
	srli t2, t0, 8
	sb t2, 185(s2)
	srli t2, t0, 16
	sb t2, 186(s2)
	srli t2, t0, 24
	sb t2, 187(s2)
	lbu t0, 188(s2)
	lbu t2, 189(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 190(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 191(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1268(s4)
	lbu t2, 1269(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1270(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1271(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 188(s2)
	srli t2, t0, 8
	sb t2, 189(s2)
	srli t2, t0, 16
	sb t2, 190(s2)
	srli t2, t0, 24
	sb t2, 191(s2)
	lbu t0, 192(s2)
	lbu t2, 193(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 194(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 195(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1272(s4)
	lbu t2, 1273(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1274(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1275(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 192(s2)
	srli t2, t0, 8
	sb t2, 193(s2)
	srli t2, t0, 16
	sb t2, 194(s2)
	srli t2, t0, 24
	sb t2, 195(s2)
	lbu t0, 196(s2)
	lbu t2, 197(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 198(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 199(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1276(s4)
	lbu t2, 1277(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1278(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1279(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 196(s2)
	srli t2, t0, 8
	sb t2, 197(s2)
	srli t2, t0, 16
	sb t2, 198(s2)
	srli t2, t0, 24
	sb t2, 199(s2)
	lbu t0, 200(s2)
	lbu t2, 201(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 202(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 203(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1280(s4)
	lbu t2, 1281(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1282(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1283(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 200(s2)
	srli t2, t0, 8
	sb t2, 201(s2)
	srli t2, t0, 16
	sb t2, 202(s2)
	srli t2, t0, 24
	sb t2, 203(s2)
	lbu t0, 204(s2)
	lbu t2, 205(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 206(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 207(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1284(s4)
	lbu t2, 1285(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1286(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1287(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 204(s2)
	srli t2, t0, 8
	sb t2, 205(s2)
	srli t2, t0, 16
	sb t2, 206(s2)
	srli t2, t0, 24
	sb t2, 207(s2)
	lbu t0, 208(s2)
	lbu t2, 209(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 210(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 211(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1288(s4)
	lbu t2, 1289(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1290(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1291(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 208(s2)
	srli t2, t0, 8
	sb t2, 209(s2)
	srli t2, t0, 16
	sb t2, 210(s2)
	srli t2, t0, 24
	sb t2, 211(s2)
	lbu t0, 212(s2)
	lbu t2, 213(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 214(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 215(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1292(s4)
	lbu t2, 1293(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1294(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1295(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 212(s2)
	srli t2, t0, 8
	sb t2, 213(s2)
	srli t2, t0, 16
	sb t2, 214(s2)
	srli t2, t0, 24
	sb t2, 215(s2)
	lbu t0, 216(s2)
	lbu t2, 217(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 218(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 219(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1296(s4)
	lbu t2, 1297(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1298(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1299(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 216(s2)
	srli t2, t0, 8
	sb t2, 217(s2)
	srli t2, t0, 16
	sb t2, 218(s2)
	srli t2, t0, 24
	sb t2, 219(s2)
	lbu t0, 220(s2)
	lbu t2, 221(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 222(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 223(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1300(s4)
	lbu t2, 1301(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1302(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1303(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 220(s2)
	srli t2, t0, 8
	sb t2, 221(s2)
	srli t2, t0, 16
	sb t2, 222(s2)
	srli t2, t0, 24
	sb t2, 223(s2)
	lbu t0, 224(s2)
	lbu t2, 225(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 226(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 227(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1304(s4)
	lbu t2, 1305(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1306(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1307(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 224(s2)
	srli t2, t0, 8
	sb t2, 225(s2)
	srli t2, t0, 16
	sb t2, 226(s2)
	srli t2, t0, 24
	sb t2, 227(s2)
	lbu t0, 228(s2)
	lbu t2, 229(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 230(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 231(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1308(s4)
	lbu t2, 1309(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1310(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1311(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 228(s2)
	srli t2, t0, 8
	sb t2, 229(s2)
	srli t2, t0, 16
	sb t2, 230(s2)
	srli t2, t0, 24
	sb t2, 231(s2)
	lbu t0, 232(s2)
	lbu t2, 233(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 234(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 235(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1312(s4)
	lbu t2, 1313(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1314(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1315(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 232(s2)
	srli t2, t0, 8
	sb t2, 233(s2)
	srli t2, t0, 16
	sb t2, 234(s2)
	srli t2, t0, 24
	sb t2, 235(s2)
	lbu t0, 236(s2)
	lbu t2, 237(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 238(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 239(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1316(s4)
	lbu t2, 1317(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1318(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1319(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 236(s2)
	srli t2, t0, 8
	sb t2, 237(s2)
	srli t2, t0, 16
	sb t2, 238(s2)
	srli t2, t0, 24
	sb t2, 239(s2)
	lbu t0, 240(s2)
	lbu t2, 241(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 242(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 243(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1320(s4)
	lbu t2, 1321(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1322(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1323(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 240(s2)
	srli t2, t0, 8
	sb t2, 241(s2)
	srli t2, t0, 16
	sb t2, 242(s2)
	srli t2, t0, 24
	sb t2, 243(s2)
	lbu t0, 244(s2)
	lbu t2, 245(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 246(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 247(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1324(s4)
	lbu t2, 1325(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1326(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1327(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 244(s2)
	srli t2, t0, 8
	sb t2, 245(s2)
	srli t2, t0, 16
	sb t2, 246(s2)
	srli t2, t0, 24
	sb t2, 247(s2)
	lbu t0, 248(s2)
	lbu t2, 249(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 250(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 251(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1328(s4)
	lbu t2, 1329(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1330(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1331(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 248(s2)
	srli t2, t0, 8
	sb t2, 249(s2)
	srli t2, t0, 16
	sb t2, 250(s2)
	srli t2, t0, 24
	sb t2, 251(s2)
	lbu t0, 252(s2)
	lbu t2, 253(s2)
	slli t2, t2, 8
	or t0, t0, t2
	lbu t2, 254(s2)
	slli t2, t2, 16
	or t0, t0, t2
	lbu t2, 255(s2)
	slli t2, t2, 24
	or t0, t0, t2
	lbu t1, 1332(s4)
	lbu t2, 1333(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1334(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1335(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 252(s2)
	srli t2, t0, 8
	sb t2, 253(s2)
	srli t2, t0, 16
	sb t2, 254(s2)
	srli t2, t0, 24
	sb t2, 255(s2)
	addi s2, s2, 256
	addi s3, s3, -16
	srli t0, s3, 4
	bnez t0, 22b
	j 21f
20:
21:
	beqz s3, 26f
28:
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
	sb t0, 1080(s4)
	srli t2, t0, 8
	sb t2, 1081(s4)
	srli t2, t0, 16
	sb t2, 1082(s4)
	srli t2, t0, 24
	sb t2, 1083(s4)
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
	sb t0, 1084(s4)
	srli t2, t0, 8
	sb t2, 1085(s4)
	srli t2, t0, 16
	sb t2, 1086(s4)
	srli t2, t0, 24
	sb t2, 1087(s4)
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
	sb t0, 1088(s4)
	srli t2, t0, 8
	sb t2, 1089(s4)
	srli t2, t0, 16
	sb t2, 1090(s4)
	srli t2, t0, 24
	sb t2, 1091(s4)
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
	sb t0, 1092(s4)
	srli t2, t0, 8
	sb t2, 1093(s4)
	srli t2, t0, 16
	sb t2, 1094(s4)
	srli t2, t0, 24
	sb t2, 1095(s4)
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
	addi t0, s4, 48
	addi a5, t0, 0
	sd s0, 936(a5)
	sd s1, 944(a5)
	sd s2, 952(a5)
	sd s3, 960(a5)
	sd s4, 968(a5)
	sd s5, 976(a5)
	sd s6, 984(a5)
	sd s7, 992(a5)
	sd s8, 1000(a5)
	sd s9, 1008(a5)
	sd s10, 1016(a5)
	sd s11, 1024(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 832(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 840(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 848(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 856(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 1044496
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 864(a5)
	lui t0, 851917
	addiw t0, t0, -4
	slli t0, t0, 32
	lui t1, 851917
	addiw t1, t1, -4
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 872(a5)
	lui t0, 3892
	addiw t0, t0, -13
	slli t0, t0, 32
	lui t1, 3892
	addiw t1, t1, -13
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 880(a5)
	lui t0, 258048
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 258048
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 888(a5)
	lui t0, 16
	addiw t0, t0, -817
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -817
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 896(a5)
	lui t0, 1035504
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1035504
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 904(a5)
	lui t0, 0
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 63
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 912(a5)
	lui t0, 996351
	addiw t0, t0, 768
	slli t0, t0, 32
	lui t1, 996351
	addiw t1, t1, 768
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 920(a5)
	lui t0, 946878
	addiw t0, t0, 1835
	slli t0, t0, 32
	lui t1, 946878
	addiw t1, t1, 1835
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 928(a5)
	addi a3, a5, 832
	sd ra, 1288(a5)
	addi a1, s1, 0
	addi a2, s2, 0
	addi ra, s3, 0
	addi a0, a0, 0
	addi t2, zero, 16
	addi t3, a5, 1032
	addi t4, a5, 0
29:
	lbu t0, 0(t3)
	slli t0, t0, 24
	lbu t1, 1(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 2(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 3(t3)
	or t0, t0, t1
	sw t0, 576(t4)
	lbu t0, 4(t3)
	slli t0, t0, 24
	lbu t1, 5(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 6(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 7(t3)
	or t0, t0, t1
	sw t0, 640(t4)
	lbu t0, 8(t3)
	slli t0, t0, 24
	lbu t1, 9(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 10(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 11(t3)
	or t0, t0, t1
	sw t0, 704(t4)
	lbu t0, 12(t3)
	slli t0, t0, 24
	lbu t1, 13(t3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 14(t3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 15(t3)
	or t0, t0, t1
	sw t0, 768(t4)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 29b
	addi a4, zero, 16
210:
	lbu t5, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or t5, t5, t0
	lbu t6, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t6, t6, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t6, t6, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t6, t6, t0
	lwu t0, 704(a5)
	xor t0, t0, t5
	sw t0, 384(a5)
	lwu t1, 768(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 320(a5)
	lwu t0, 708(a5)
	xor t0, t0, t5
	sw t0, 388(a5)
	lwu t1, 772(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 324(a5)
	lwu t0, 712(a5)
	xor t0, t0, t5
	sw t0, 392(a5)
	lwu t1, 776(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 328(a5)
	lwu t0, 716(a5)
	xor t0, t0, t5
	sw t0, 396(a5)
	lwu t1, 780(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 332(a5)
	lwu t0, 720(a5)
	xor t0, t0, t5
	sw t0, 400(a5)
	lwu t1, 784(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 336(a5)
	lwu t0, 724(a5)
	xor t0, t0, t5
	sw t0, 404(a5)
	lwu t1, 788(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 340(a5)
	lwu t0, 728(a5)
	xor t0, t0, t5
	sw t0, 408(a5)
	lwu t1, 792(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 344(a5)
	lwu t0, 732(a5)
	xor t0, t0, t5
	sw t0, 412(a5)
	lwu t1, 796(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 348(a5)
	lwu t0, 736(a5)
	xor t0, t0, t5
	sw t0, 416(a5)
	lwu t1, 800(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 352(a5)
	lwu t0, 740(a5)
	xor t0, t0, t5
	sw t0, 420(a5)
	lwu t1, 804(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 356(a5)
	lwu t0, 744(a5)
	xor t0, t0, t5
	sw t0, 424(a5)
	lwu t1, 808(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 360(a5)
	lwu t0, 748(a5)
	xor t0, t0, t5
	sw t0, 428(a5)
	lwu t1, 812(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 364(a5)
	lwu t0, 752(a5)
	xor t0, t0, t5
	sw t0, 432(a5)
	lwu t1, 816(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 368(a5)
	lwu t0, 756(a5)
	xor t0, t0, t5
	sw t0, 436(a5)
	lwu t1, 820(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 372(a5)
	lwu t0, 760(a5)
	xor t0, t0, t5
	sw t0, 440(a5)
	lwu t1, 824(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 376(a5)
	lwu t0, 764(a5)
	xor t0, t0, t5
	sw t0, 444(a5)
	lwu t1, 828(a5)
	xor t0, t0, t1
	xor t0, t0, t6
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 448(a5)
	lwu t1, 384(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 452(a5)
	lwu t1, 388(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 456(a5)
	lwu t1, 392(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 460(a5)
	lwu t1, 396(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 464(a5)
	lwu t1, 400(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 468(a5)
	lwu t1, 404(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 472(a5)
	lwu t1, 408(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 476(a5)
	lwu t1, 412(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 480(a5)
	lwu t1, 416(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 484(a5)
	lwu t1, 420(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 488(a5)
	lwu t1, 424(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 492(a5)
	lwu t1, 428(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 496(a5)
	lwu t1, 432(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 500(a5)
	lwu t1, 436(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 504(a5)
	lwu t1, 440(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 508(a5)
	lwu t1, 444(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	sw t0, 512(a5)
	lwu t1, 448(a5)
	add t0, t0, t1
	sw t0, 320(a5)
	lwu t0, 324(a5)
	sw t0, 516(a5)
	lwu t1, 452(a5)
	add t0, t0, t1
	sw t0, 324(a5)
	lwu t0, 328(a5)
	sw t0, 520(a5)
	lwu t1, 456(a5)
	add t0, t0, t1
	sw t0, 328(a5)
	lwu t0, 332(a5)
	sw t0, 524(a5)
	lwu t1, 460(a5)
	add t0, t0, t1
	sw t0, 332(a5)
	lwu t0, 336(a5)
	sw t0, 528(a5)
	lwu t1, 464(a5)
	add t0, t0, t1
	sw t0, 336(a5)
	lwu t0, 340(a5)
	sw t0, 532(a5)
	lwu t1, 468(a5)
	add t0, t0, t1
	sw t0, 340(a5)
	lwu t0, 344(a5)
	sw t0, 536(a5)
	lwu t1, 472(a5)
	add t0, t0, t1
	sw t0, 344(a5)
	lwu t0, 348(a5)
	sw t0, 540(a5)
	lwu t1, 476(a5)
	add t0, t0, t1
	sw t0, 348(a5)
	lwu t0, 352(a5)
	sw t0, 544(a5)
	lwu t1, 480(a5)
	add t0, t0, t1
	sw t0, 352(a5)
	lwu t0, 356(a5)
	sw t0, 548(a5)
	lwu t1, 484(a5)
	add t0, t0, t1
	sw t0, 356(a5)
	lwu t0, 360(a5)
	sw t0, 552(a5)
	lwu t1, 488(a5)
	add t0, t0, t1
	sw t0, 360(a5)
	lwu t0, 364(a5)
	sw t0, 556(a5)
	lwu t1, 492(a5)
	add t0, t0, t1
	sw t0, 364(a5)
	lwu t0, 368(a5)
	sw t0, 560(a5)
	lwu t1, 496(a5)
	add t0, t0, t1
	sw t0, 368(a5)
	lwu t0, 372(a5)
	sw t0, 564(a5)
	lwu t1, 500(a5)
	add t0, t0, t1
	sw t0, 372(a5)
	lwu t0, 376(a5)
	sw t0, 568(a5)
	lwu t1, 504(a5)
	add t0, t0, t1
	sw t0, 376(a5)
	lwu t0, 380(a5)
	sw t0, 572(a5)
	lwu t1, 508(a5)
	add t0, t0, t1
	sw t0, 380(a5)
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	addi s0, t1, 0
	xor s0, s0, t2
	xor s0, s0, t4
	addi s1, t3, 0
	xor s1, s1, t4
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t5, 0
	xor s2, s2, t6
	xor s2, s2, a7
	addi s3, t2, 0
	xor s3, s3, t3
	xor s3, s3, t4
	xor s3, s3, t6
	addi s4, t2, 0
	xor s4, s4, t3
	xor s4, s4, t5
	addi s5, t4, 0
	xor s5, s5, t5
	addi s6, t3, 0
	xor s6, s6, t4
	xor s6, s6, t5
	xor s6, s6, t6
	addi s7, t5, 0
	xor s7, s7, t6
	xor s7, s7, a6
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	addi t1, s0, 0
	addi t2, s1, 0
	addi t3, s2, 0
	addi t4, s3, 0
	addi t5, s4, 0
	addi t6, s5, 0
	addi a6, s6, 0
	addi a7, s7, 0
	ld s8, 24(a3)
	ld s9, 32(a3)
	and s0, t2, s9
	and t0, t3, s8
	xor s0, s0, t0
	and t0, t4, s9
	xor s0, s0, t0
	and t0, t5, s8
	xor s0, s0, t0
	and t0, t6, s8
	xor s0, s0, t0
	and t0, a6, s8
	xor s0, s0, t0
	and s1, t2, s9
	and t0, t3, s8
	xor s1, s1, t0
	xor s1, s1, t5
	and t0, t6, s9
	xor s1, s1, t0
	xor s1, s1, a6
	xor s1, s1, a7
	addi s2, t1, 0
	and t0, t2, s8
	xor s2, s2, t0
	and t0, t3, s9
	xor s2, s2, t0
	and t0, t4, s9
	xor s2, s2, t0
	xor s2, s2, t5
	xor s2, s2, a6
	addi s3, t1, 0
	and t0, t2, s9
	xor s3, s3, t0
	and t0, t3, s8
	xor s3, s3, t0
	and t0, t4, s9
	xor s3, s3, t0
	xor s3, s3, t5
	xor s3, s3, t6
	xor s3, s3, a6
	and t0, a7, s8
	xor s3, s3, t0
	and s4, t1, s8
	and t0, t3, s8
	xor s4, s4, t0
	xor s4, s4, t4
	and t0, t5, s8
	xor s4, s4, t0
	xor s4, s4, a6
	and t0, a7, s9
	xor s4, s4, t0
	and s5, t1, s8
	and t0, t2, s8
	xor s5, s5, t0
	xor s5, s5, t4
	and t0, t5, s9
	xor s5, s5, t0
	xor s5, s5, t6
	xor s5, s5, a6
	and s6, t1, s8
	and t0, t2, s9
	xor s6, s6, t0
	and t0, t3, s9
	xor s6, s6, t0
	and t0, t4, s9
	xor s6, s6, t0
	and t0, t5, s8
	xor s6, s6, t0
	and t0, t6, s8
	xor s6, s6, t0
	xor s6, s6, a6
	and s7, t2, s8
	xor s7, s7, t4
	and t0, a6, s8
	xor s7, s7, t0
	and t0, a7, s8
	xor s7, s7, t0
	ld t6, 0(a3)
	ld a6, 8(a3)
	ld a7, 16(a3)
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
	ld t2, 40(a3)
	ld t3, 48(a3)
	ld t6, 56(a3)
	ld t4, 64(a3)
	ld a6, 72(a3)
	ld t5, 80(a3)
	ld a7, 88(a3)
	ld s8, 96(a3)
	and t1, s0, t2
	srli t0, s0, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s0, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s0, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s0, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s0, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s0, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 320(a5)
	and t1, s1, t2
	srli t0, s1, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s1, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s1, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s1, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s1, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s1, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 328(a5)
	and t1, s2, t2
	srli t0, s2, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s2, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s2, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s2, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s2, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s2, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 336(a5)
	and t1, s3, t2
	srli t0, s3, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s3, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s3, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s3, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s3, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s3, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 344(a5)
	and t1, s4, t2
	srli t0, s4, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s4, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s4, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s4, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s4, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s4, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 352(a5)
	and t1, s5, t2
	srli t0, s5, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s5, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s5, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s5, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s5, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s5, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 360(a5)
	and t1, s6, t2
	srli t0, s6, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s6, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s6, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s6, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s6, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s6, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 368(a5)
	and t1, s7, t2
	srli t0, s7, 8
	and t0, t0, t3
	xor t1, t1, t0
	slli t0, s7, 24
	and t0, t0, t6
	xor t1, t1, t0
	srli t0, s7, 16
	and t0, t0, t4
	xor t1, t1, t0
	slli t0, s7, 16
	and t0, t0, a6
	xor t1, t1, t0
	srli t0, s7, 24
	and t0, t0, t5
	xor t1, t1, t0
	slli t0, s7, 8
	and t0, t0, a7
	xor t1, t1, t0
	xor t1, t1, s8
	sd t1, 376(a5)
	lwu t0, 320(a5)
	lwu t1, 640(a5)
	xor t1, t1, t0
	sw t1, 640(a5)
	lwu t1, 512(a5)
	add t0, t0, t1
	lwu t1, 576(a5)
	xor t0, t0, t1
	sw t0, 576(a5)
	lwu t0, 324(a5)
	lwu t1, 644(a5)
	xor t1, t1, t0
	sw t1, 644(a5)
	lwu t1, 516(a5)
	add t0, t0, t1
	lwu t1, 580(a5)
	xor t0, t0, t1
	sw t0, 580(a5)
	lwu t0, 328(a5)
	lwu t1, 648(a5)
	xor t1, t1, t0
	sw t1, 648(a5)
	lwu t1, 520(a5)
	add t0, t0, t1
	lwu t1, 584(a5)
	xor t0, t0, t1
	sw t0, 584(a5)
	lwu t0, 332(a5)
	lwu t1, 652(a5)
	xor t1, t1, t0
	sw t1, 652(a5)
	lwu t1, 524(a5)
	add t0, t0, t1
	lwu t1, 588(a5)
	xor t0, t0, t1
	sw t0, 588(a5)
	lwu t0, 336(a5)
	lwu t1, 656(a5)
	xor t1, t1, t0
	sw t1, 656(a5)
	lwu t1, 528(a5)
	add t0, t0, t1
	lwu t1, 592(a5)
	xor t0, t0, t1
	sw t0, 592(a5)
	lwu t0, 340(a5)
	lwu t1, 660(a5)
	xor t1, t1, t0
	sw t1, 660(a5)
	lwu t1, 532(a5)
	add t0, t0, t1
	lwu t1, 596(a5)
	xor t0, t0, t1
	sw t0, 596(a5)
	lwu t0, 344(a5)
	lwu t1, 664(a5)
	xor t1, t1, t0
	sw t1, 664(a5)
	lwu t1, 536(a5)
	add t0, t0, t1
	lwu t1, 600(a5)
	xor t0, t0, t1
	sw t0, 600(a5)
	lwu t0, 348(a5)
	lwu t1, 668(a5)
	xor t1, t1, t0
	sw t1, 668(a5)
	lwu t1, 540(a5)
	add t0, t0, t1
	lwu t1, 604(a5)
	xor t0, t0, t1
	sw t0, 604(a5)
	lwu t0, 352(a5)
	lwu t1, 672(a5)
	xor t1, t1, t0
	sw t1, 672(a5)
	lwu t1, 544(a5)
	add t0, t0, t1
	lwu t1, 608(a5)
	xor t0, t0, t1
	sw t0, 608(a5)
	lwu t0, 356(a5)
	lwu t1, 676(a5)
	xor t1, t1, t0
	sw t1, 676(a5)
	lwu t1, 548(a5)
	add t0, t0, t1
	lwu t1, 612(a5)
	xor t0, t0, t1
	sw t0, 612(a5)
	lwu t0, 360(a5)
	lwu t1, 680(a5)
	xor t1, t1, t0
	sw t1, 680(a5)
	lwu t1, 552(a5)
	add t0, t0, t1
	lwu t1, 616(a5)
	xor t0, t0, t1
	sw t0, 616(a5)
	lwu t0, 364(a5)
	lwu t1, 684(a5)
	xor t1, t1, t0
	sw t1, 684(a5)
	lwu t1, 556(a5)
	add t0, t0, t1
	lwu t1, 620(a5)
	xor t0, t0, t1
	sw t0, 620(a5)
	lwu t0, 368(a5)
	lwu t1, 688(a5)
	xor t1, t1, t0
	sw t1, 688(a5)
	lwu t1, 560(a5)
	add t0, t0, t1
	lwu t1, 624(a5)
	xor t0, t0, t1
	sw t0, 624(a5)
	lwu t0, 372(a5)
	lwu t1, 692(a5)
	xor t1, t1, t0
	sw t1, 692(a5)
	lwu t1, 564(a5)
	add t0, t0, t1
	lwu t1, 628(a5)
	xor t0, t0, t1
	sw t0, 628(a5)
	lwu t0, 376(a5)
	lwu t1, 696(a5)
	xor t1, t1, t0
	sw t1, 696(a5)
	lwu t1, 568(a5)
	add t0, t0, t1
	lwu t1, 632(a5)
	xor t0, t0, t1
	sw t0, 632(a5)
	lwu t0, 380(a5)
	lwu t1, 700(a5)
	xor t1, t1, t0
	sw t1, 700(a5)
	lwu t1, 572(a5)
	add t0, t0, t1
	lwu t1, 636(a5)
	xor t0, t0, t1
	sw t0, 636(a5)
	ld t0, 576(a5)
	ld t1, 704(a5)
	sd t1, 576(a5)
	sd t0, 704(a5)
	ld t0, 584(a5)
	ld t1, 712(a5)
	sd t1, 584(a5)
	sd t0, 712(a5)
	ld t0, 592(a5)
	ld t1, 720(a5)
	sd t1, 592(a5)
	sd t0, 720(a5)
	ld t0, 600(a5)
	ld t1, 728(a5)
	sd t1, 600(a5)
	sd t0, 728(a5)
	ld t0, 608(a5)
	ld t1, 736(a5)
	sd t1, 608(a5)
	sd t0, 736(a5)
	ld t0, 616(a5)
	ld t1, 744(a5)
	sd t1, 616(a5)
	sd t0, 744(a5)
	ld t0, 624(a5)
	ld t1, 752(a5)
	sd t1, 624(a5)
	sd t0, 752(a5)
	ld t0, 632(a5)
	ld t1, 760(a5)
	sd t1, 632(a5)
	sd t0, 760(a5)
	ld t0, 640(a5)
	ld t1, 768(a5)
	sd t1, 640(a5)
	sd t0, 768(a5)
	ld t0, 648(a5)
	ld t1, 776(a5)
	sd t1, 648(a5)
	sd t0, 776(a5)
	ld t0, 656(a5)
	ld t1, 784(a5)
	sd t1, 656(a5)
	sd t0, 784(a5)
	ld t0, 664(a5)
	ld t1, 792(a5)
	sd t1, 664(a5)
	sd t0, 792(a5)
	ld t0, 672(a5)
	ld t1, 800(a5)
	sd t1, 672(a5)
	sd t0, 800(a5)
	ld t0, 680(a5)
	ld t1, 808(a5)
	sd t1, 680(a5)
	sd t0, 808(a5)
	ld t0, 688(a5)
	ld t1, 816(a5)
	sd t1, 688(a5)
	sd t0, 816(a5)
	ld t0, 696(a5)
	ld t1, 824(a5)
	sd t1, 696(a5)
	sd t0, 824(a5)
	addi a0, a0, 8
	addi a4, a4, -1
	bnez a4, 210b
	addi a0, a0, -128
	addi t2, zero, 16
	addi t3, a5, 1032
	addi t4, a5, 0
211:
	lwu t0, 704(t4)
	srli t1, t0, 24
	sb t1, 0(t3)
	srli t1, t0, 16
	sb t1, 1(t3)
	srli t1, t0, 8
	sb t1, 2(t3)
	srli t1, t0, 0
	sb t1, 3(t3)
	lwu t0, 768(t4)
	srli t1, t0, 24
	sb t1, 4(t3)
	srli t1, t0, 16
	sb t1, 5(t3)
	srli t1, t0, 8
	sb t1, 6(t3)
	srli t1, t0, 0
	sb t1, 7(t3)
	lwu t0, 576(t4)
	srli t1, t0, 24
	sb t1, 8(t3)
	srli t1, t0, 16
	sb t1, 9(t3)
	srli t1, t0, 8
	sb t1, 10(t3)
	srli t1, t0, 0
	sb t1, 11(t3)
	lwu t0, 640(t4)
	srli t1, t0, 24
	sb t1, 12(t3)
	srli t1, t0, 16
	sb t1, 13(t3)
	srli t1, t0, 8
	sb t1, 14(t3)
	srli t1, t0, 0
	sb t1, 15(t3)
	addi t3, t3, 16
	addi t4, t4, 4
	addi t2, t2, -1
	bnez t2, 211b
	addi a0, a0, 0
	ld s0, 936(a5)
	ld s1, 944(a5)
	ld s2, 952(a5)
	ld s3, 960(a5)
	ld s4, 968(a5)
	ld s5, 976(a5)
	ld s6, 984(a5)
	ld s7, 992(a5)
	ld s8, 1000(a5)
	ld s9, 1008(a5)
	ld s10, 1016(a5)
	ld s11, 1024(a5)
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, ra, 0
	ld ra, 1288(a5)
	addi s4, a5, -48
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
	lbu t1, 1080(s4)
	lbu t2, 1081(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1082(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1083(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 0(s2)
	srli t2, t0, 8
	sb t2, 1(s2)
	srli t2, t0, 16
	sb t2, 2(s2)
	srli t2, t0, 24
	sb t2, 3(s2)
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
	lbu t1, 1084(s4)
	lbu t2, 1085(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1086(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1087(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 4(s2)
	srli t2, t0, 8
	sb t2, 5(s2)
	srli t2, t0, 16
	sb t2, 6(s2)
	srli t2, t0, 24
	sb t2, 7(s2)
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
	lbu t1, 1088(s4)
	lbu t2, 1089(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1090(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1091(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 8(s2)
	srli t2, t0, 8
	sb t2, 9(s2)
	srli t2, t0, 16
	sb t2, 10(s2)
	srli t2, t0, 24
	sb t2, 11(s2)
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
	lbu t1, 1092(s4)
	lbu t2, 1093(s4)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 1094(s4)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 1095(s4)
	slli t2, t2, 24
	or t1, t1, t2
	xor t0, t0, t1
	sb t0, 12(s2)
	srli t2, t0, 8
	sb t2, 13(s2)
	srli t2, t0, 16
	sb t2, 14(s2)
	srli t2, t0, 24
	sb t2, 15(s2)
	addi s2, s2, 16
	addi s3, s3, -1
	bnez s3, 28b
	j 27f
26:
27:
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
	addi t2, zero, 168
212:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 212b
	addi sp, sp, 1344
	ret
	.option pop
