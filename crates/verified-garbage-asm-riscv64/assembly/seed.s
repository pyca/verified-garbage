// The functions of `src/seed.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1040
	addi a2, sp, 0
	addi a5, a2, 0
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
	lbu t5, 0(a0)
	slli t5, t5, 8
	lbu t0, 1(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 2(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 3(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 4(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 5(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 6(a0)
	or t5, t5, t0
	slli t5, t5, 8
	lbu t0, 7(a0)
	or t5, t5, t0
	lbu t6, 8(a0)
	slli t6, t6, 8
	lbu t0, 9(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 10(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 11(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 12(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 13(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 14(a0)
	or t6, t6, t0
	slli t6, t6, 8
	lbu t0, 15(a0)
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 648056
	addiw t2, t2, -1607
	sub t0, t0, t2
	sw t0, 320(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 324(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 247535
	addiw t2, t2, 883
	sub t0, t0, t2
	sw t0, 328(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 332(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 495070
	addiw t2, t2, 1766
	sub t0, t0, t2
	sw t0, 336(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 340(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 990141
	addiw t2, t2, -564
	sub t0, t0, t2
	sw t0, 344(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 348(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 931706
	addiw t2, t2, -1127
	sub t0, t0, t2
	sw t0, 352(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 356(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 814835
	addiw t2, t2, 1843
	sub t0, t0, t2
	sw t0, 360(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 364(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 581095
	addiw t2, t2, -409
	sub t0, t0, t2
	sw t0, 368(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 372(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 113614
	addiw t2, t2, -817
	sub t0, t0, t2
	sw t0, 376(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 380(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 227228
	addiw t2, t2, -1634
	sub t0, t0, t2
	sw t0, 384(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 388(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 454455
	addiw t2, t2, 828
	sub t0, t0, t2
	sw t0, 392(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 396(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 908910
	addiw t2, t2, 1656
	sub t0, t0, t2
	sw t0, 400(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 404(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 769245
	addiw t2, t2, -783
	sub t0, t0, t2
	sw t0, 408(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 412(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 489914
	addiw t2, t2, -1565
	sub t0, t0, t2
	sw t0, 416(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 420(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 979827
	addiw t2, t2, 966
	sub t0, t0, t2
	sw t0, 424(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 428(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 911078
	addiw t2, t2, 1933
	sub t0, t0, t2
	sw t0, 432(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 436(a5)
	srli t0, t5, 8
	slli t5, t5, 56
	or t5, t5, t0
	srli t0, t5, 32
	srli t1, t6, 32
	add t0, t0, t1
	lui t2, 773581
	addiw t2, t2, -229
	sub t0, t0, t2
	sw t0, 440(a5)
	sub t0, t5, t6
	add t0, t0, t2
	sw t0, 444(a5)
	srli t0, t6, 56
	slli t6, t6, 8
	or t6, t6, t0
	addi a4, zero, 2
20:
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
	sb t0, 0(a1)
	srli t1, t0, 8
	sb t1, 1(a1)
	srli t1, t0, 16
	sb t1, 2(a1)
	srli t1, t0, 24
	sb t1, 3(a1)
	lwu t0, 324(a5)
	sb t0, 4(a1)
	srli t1, t0, 8
	sb t1, 5(a1)
	srli t1, t0, 16
	sb t1, 6(a1)
	srli t1, t0, 24
	sb t1, 7(a1)
	lwu t0, 328(a5)
	sb t0, 8(a1)
	srli t1, t0, 8
	sb t1, 9(a1)
	srli t1, t0, 16
	sb t1, 10(a1)
	srli t1, t0, 24
	sb t1, 11(a1)
	lwu t0, 332(a5)
	sb t0, 12(a1)
	srli t1, t0, 8
	sb t1, 13(a1)
	srli t1, t0, 16
	sb t1, 14(a1)
	srli t1, t0, 24
	sb t1, 15(a1)
	lwu t0, 336(a5)
	sb t0, 16(a1)
	srli t1, t0, 8
	sb t1, 17(a1)
	srli t1, t0, 16
	sb t1, 18(a1)
	srli t1, t0, 24
	sb t1, 19(a1)
	lwu t0, 340(a5)
	sb t0, 20(a1)
	srli t1, t0, 8
	sb t1, 21(a1)
	srli t1, t0, 16
	sb t1, 22(a1)
	srli t1, t0, 24
	sb t1, 23(a1)
	lwu t0, 344(a5)
	sb t0, 24(a1)
	srli t1, t0, 8
	sb t1, 25(a1)
	srli t1, t0, 16
	sb t1, 26(a1)
	srli t1, t0, 24
	sb t1, 27(a1)
	lwu t0, 348(a5)
	sb t0, 28(a1)
	srli t1, t0, 8
	sb t1, 29(a1)
	srli t1, t0, 16
	sb t1, 30(a1)
	srli t1, t0, 24
	sb t1, 31(a1)
	lwu t0, 352(a5)
	sb t0, 32(a1)
	srli t1, t0, 8
	sb t1, 33(a1)
	srli t1, t0, 16
	sb t1, 34(a1)
	srli t1, t0, 24
	sb t1, 35(a1)
	lwu t0, 356(a5)
	sb t0, 36(a1)
	srli t1, t0, 8
	sb t1, 37(a1)
	srli t1, t0, 16
	sb t1, 38(a1)
	srli t1, t0, 24
	sb t1, 39(a1)
	lwu t0, 360(a5)
	sb t0, 40(a1)
	srli t1, t0, 8
	sb t1, 41(a1)
	srli t1, t0, 16
	sb t1, 42(a1)
	srli t1, t0, 24
	sb t1, 43(a1)
	lwu t0, 364(a5)
	sb t0, 44(a1)
	srli t1, t0, 8
	sb t1, 45(a1)
	srli t1, t0, 16
	sb t1, 46(a1)
	srli t1, t0, 24
	sb t1, 47(a1)
	lwu t0, 368(a5)
	sb t0, 48(a1)
	srli t1, t0, 8
	sb t1, 49(a1)
	srli t1, t0, 16
	sb t1, 50(a1)
	srli t1, t0, 24
	sb t1, 51(a1)
	lwu t0, 372(a5)
	sb t0, 52(a1)
	srli t1, t0, 8
	sb t1, 53(a1)
	srli t1, t0, 16
	sb t1, 54(a1)
	srli t1, t0, 24
	sb t1, 55(a1)
	lwu t0, 376(a5)
	sb t0, 56(a1)
	srli t1, t0, 8
	sb t1, 57(a1)
	srli t1, t0, 16
	sb t1, 58(a1)
	srli t1, t0, 24
	sb t1, 59(a1)
	lwu t0, 380(a5)
	sb t0, 60(a1)
	srli t1, t0, 8
	sb t1, 61(a1)
	srli t1, t0, 16
	sb t1, 62(a1)
	srli t1, t0, 24
	sb t1, 63(a1)
	addi a1, a1, 64
	addi a4, a4, -1
	bnez a4, 21f
	j 22f
21:
	lwu t0, 384(a5)
	sw t0, 320(a5)
	lwu t0, 388(a5)
	sw t0, 324(a5)
	lwu t0, 392(a5)
	sw t0, 328(a5)
	lwu t0, 396(a5)
	sw t0, 332(a5)
	lwu t0, 400(a5)
	sw t0, 336(a5)
	lwu t0, 404(a5)
	sw t0, 340(a5)
	lwu t0, 408(a5)
	sw t0, 344(a5)
	lwu t0, 412(a5)
	sw t0, 348(a5)
	lwu t0, 416(a5)
	sw t0, 352(a5)
	lwu t0, 420(a5)
	sw t0, 356(a5)
	lwu t0, 424(a5)
	sw t0, 360(a5)
	lwu t0, 428(a5)
	sw t0, 364(a5)
	lwu t0, 432(a5)
	sw t0, 368(a5)
	lwu t0, 436(a5)
	sw t0, 372(a5)
	lwu t0, 440(a5)
	sw t0, 376(a5)
	lwu t0, 444(a5)
	sw t0, 380(a5)
22:
	bnez a4, 20b
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
	addi sp, sp, 1040
	ret
	.option pop

vg_seed_ecb_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1040
	addi a3, sp, 0
	addi a5, a3, 0
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
	addi a0, a0, 0
	beqz a2, 20f
22:
	srli t2, a2, 4
	bnez t2, 23f
	addi t2, a2, 0
	j 24f
23:
	addi t2, zero, 16
24:
	addi t3, a1, 0
	addi t4, a5, 0
25:
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
	bnez t2, 25b
	addi a4, zero, 16
26:
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
	bnez a4, 26b
	addi a0, a0, -128
	srli t2, a2, 4
	bnez t2, 27f
	addi t2, a2, 0
	j 28f
27:
	addi t2, zero, 16
28:
	addi t3, a1, 0
	addi t4, a5, 0
29:
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
	bnez t2, 29b
	srli t2, a2, 4
	bnez t2, 210f
	addi t2, a2, 0
	j 211f
210:
	addi t2, zero, 16
211:
	addi a1, t3, 0
	sub a2, a2, t2
	bnez a2, 22b
	j 21f
20:
21:
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
	addi sp, sp, 1040
	ret
	.option pop

vg_seed_ecb_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -1040
	addi a3, sp, 0
	addi a5, a3, 0
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
	addi a0, a0, 120
	beqz a2, 20f
22:
	srli t2, a2, 4
	bnez t2, 23f
	addi t2, a2, 0
	j 24f
23:
	addi t2, zero, 16
24:
	addi t3, a1, 0
	addi t4, a5, 0
25:
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
	bnez t2, 25b
	addi a4, zero, 16
26:
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
	addi a0, a0, -8
	addi a4, a4, -1
	bnez a4, 26b
	addi a0, a0, 128
	srli t2, a2, 4
	bnez t2, 27f
	addi t2, a2, 0
	j 28f
27:
	addi t2, zero, 16
28:
	addi t3, a1, 0
	addi t4, a5, 0
29:
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
	bnez t2, 29b
	srli t2, a2, 4
	bnez t2, 210f
	addi t2, a2, 0
	j 211f
210:
	addi t2, zero, 16
211:
	addi a1, t3, 0
	sub a2, a2, t2
	bnez a2, 22b
	j 21f
20:
21:
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
	addi sp, sp, 1040
	ret
	.option pop
