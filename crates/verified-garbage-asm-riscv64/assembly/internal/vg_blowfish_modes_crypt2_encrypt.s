// The functions of `src/internal/vg_blowfish_modes_crypt2_encrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_modes_crypt2_encrypt:
	.option push
	.option arch, +m, +c
	addi a7, s4, 64
	addi a1, s4, 48
	addi t0, a7, 2047
	addi t0, t0, 2047
	addi t0, t0, 74
	sd s0, 0(t0)
	sd s5, 8(t0)
	sd s6, 16(t0)
	sd s7, 24(t0)
	sd s8, 32(t0)
	sd s9, 40(t0)
	sd s10, 48(t0)
	sd s11, 56(t0)
	sd ra, 64(t0)
	addi s0, s1, 0
	addi s11, s2, 0
	addi ra, s3, 0
	lbu a3, 0(a1)
	slli a3, a3, 24
	lbu t4, 1(a1)
	slli t4, t4, 16
	or a3, a3, t4
	lbu t4, 2(a1)
	slli t4, t4, 8
	or a3, a3, t4
	lbu t4, 3(a1)
	or a3, a3, t4
	lbu a4, 4(a1)
	slli a4, a4, 24
	lbu t4, 5(a1)
	slli t4, t4, 16
	or a4, a4, t4
	lbu t4, 6(a1)
	slli t4, t4, 8
	or a4, a4, t4
	lbu t4, 7(a1)
	or a4, a4, t4
	lbu s1, 8(a1)
	slli s1, s1, 24
	lbu t4, 9(a1)
	slli t4, t4, 16
	or s1, s1, t4
	lbu t4, 10(a1)
	slli t4, t4, 8
	or s1, s1, t4
	lbu t4, 11(a1)
	or s1, s1, t4
	lbu s2, 12(a1)
	slli s2, s2, 24
	lbu t4, 13(a1)
	slli t4, t4, 16
	or s2, s2, t4
	lbu t4, 14(a1)
	slli t4, t4, 8
	or s2, s2, t4
	lbu t4, 15(a1)
	or s2, s2, t4
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
20:
	lwu t4, 0(a6)
	xor a3, a3, t4
	xor s1, s1, t4
	slli t1, a3, 32
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli s4, s1, 32
	srli s4, s4, 59
	addi s5, zero, 1
	sll s4, s5, s4
	slli t3, t1, 63
	srai t3, t3, 63
	slli s5, s4, 63
	srai s5, s5, 63
	ld t4, 0(a7)
	and t2, t4, t3
	and s6, t4, s5
	ld t4, 256(a7)
	and t5, t4, t3
	and s7, t4, s5
	ld t4, 512(a7)
	and t6, t4, t3
	and s8, t4, s5
	ld t4, 768(a7)
	and t0, t4, t3
	and s9, t4, s5
	slli t3, t1, 62
	srai t3, t3, 63
	slli s5, s4, 62
	srai s5, s5, 63
	ld t4, 8(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 264(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 520(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 776(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 61
	srai t3, t3, 63
	slli s5, s4, 61
	srai s5, s5, 63
	ld t4, 16(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 272(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 528(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 784(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 60
	srai t3, t3, 63
	slli s5, s4, 60
	srai s5, s5, 63
	ld t4, 24(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 280(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 536(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 792(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 59
	srai t3, t3, 63
	slli s5, s4, 59
	srai s5, s5, 63
	ld t4, 32(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 288(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 544(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 800(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 58
	srai t3, t3, 63
	slli s5, s4, 58
	srai s5, s5, 63
	ld t4, 40(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 296(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 552(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 808(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 57
	srai t3, t3, 63
	slli s5, s4, 57
	srai s5, s5, 63
	ld t4, 48(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 304(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 560(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 816(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 56
	srai t3, t3, 63
	slli s5, s4, 56
	srai s5, s5, 63
	ld t4, 56(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 312(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 568(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 824(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 55
	srai t3, t3, 63
	slli s5, s4, 55
	srai s5, s5, 63
	ld t4, 64(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 320(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 576(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 832(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 54
	srai t3, t3, 63
	slli s5, s4, 54
	srai s5, s5, 63
	ld t4, 72(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 328(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 584(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 840(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 53
	srai t3, t3, 63
	slli s5, s4, 53
	srai s5, s5, 63
	ld t4, 80(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 336(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 592(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 848(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 52
	srai t3, t3, 63
	slli s5, s4, 52
	srai s5, s5, 63
	ld t4, 88(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 344(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 600(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 856(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 51
	srai t3, t3, 63
	slli s5, s4, 51
	srai s5, s5, 63
	ld t4, 96(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 352(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 608(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 864(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 50
	srai t3, t3, 63
	slli s5, s4, 50
	srai s5, s5, 63
	ld t4, 104(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 360(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 616(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 872(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 49
	srai t3, t3, 63
	slli s5, s4, 49
	srai s5, s5, 63
	ld t4, 112(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 368(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 624(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 880(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 48
	srai t3, t3, 63
	slli s5, s4, 48
	srai s5, s5, 63
	ld t4, 120(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 376(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 632(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 888(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 47
	srai t3, t3, 63
	slli s5, s4, 47
	srai s5, s5, 63
	ld t4, 128(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 384(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 640(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 896(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 46
	srai t3, t3, 63
	slli s5, s4, 46
	srai s5, s5, 63
	ld t4, 136(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 392(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 648(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 904(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 45
	srai t3, t3, 63
	slli s5, s4, 45
	srai s5, s5, 63
	ld t4, 144(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 400(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 656(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 912(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 44
	srai t3, t3, 63
	slli s5, s4, 44
	srai s5, s5, 63
	ld t4, 152(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 408(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 664(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 920(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 43
	srai t3, t3, 63
	slli s5, s4, 43
	srai s5, s5, 63
	ld t4, 160(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 416(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 672(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 928(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 42
	srai t3, t3, 63
	slli s5, s4, 42
	srai s5, s5, 63
	ld t4, 168(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 424(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 680(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 936(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 41
	srai t3, t3, 63
	slli s5, s4, 41
	srai s5, s5, 63
	ld t4, 176(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 432(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 688(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 944(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 40
	srai t3, t3, 63
	slli s5, s4, 40
	srai s5, s5, 63
	ld t4, 184(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 440(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 696(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 952(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 39
	srai t3, t3, 63
	slli s5, s4, 39
	srai s5, s5, 63
	ld t4, 192(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 448(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 704(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 960(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 38
	srai t3, t3, 63
	slli s5, s4, 38
	srai s5, s5, 63
	ld t4, 200(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 456(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 712(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 968(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 37
	srai t3, t3, 63
	slli s5, s4, 37
	srai s5, s5, 63
	ld t4, 208(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 464(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 720(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 976(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 36
	srai t3, t3, 63
	slli s5, s4, 36
	srai s5, s5, 63
	ld t4, 216(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 472(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 728(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 984(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 35
	srai t3, t3, 63
	slli s5, s4, 35
	srai s5, s5, 63
	ld t4, 224(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 480(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 736(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 992(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 34
	srai t3, t3, 63
	slli s5, s4, 34
	srai s5, s5, 63
	ld t4, 232(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 488(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 744(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1000(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 33
	srai t3, t3, 63
	slli s5, s4, 33
	srai s5, s5, 63
	ld t4, 240(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 496(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 752(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1008(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 32
	srai t3, t3, 63
	slli s5, s4, 32
	srai s5, s5, 63
	ld t4, 248(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 504(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 760(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1016(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	srli t3, a3, 24
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	srli s5, s1, 24
	andi s5, s5, 7
	slli s5, s5, 3
	srl s6, s6, s5
	andi s6, s6, 255
	srl s7, s7, s5
	andi s7, s7, 255
	slli s7, s7, 8
	srl s8, s8, s5
	andi s8, s8, 255
	slli s8, s8, 16
	srl s9, s9, s5
	andi s9, s9, 255
	slli s9, s9, 24
	or s6, s6, s7
	or s8, s8, s9
	or s6, s6, s8
	or a5, t2, t2
	or s3, s6, s6
	addi a7, a7, 1024
	slli t1, a3, 40
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli s4, s1, 40
	srli s4, s4, 59
	addi s5, zero, 1
	sll s4, s5, s4
	slli t3, t1, 63
	srai t3, t3, 63
	slli s5, s4, 63
	srai s5, s5, 63
	ld t4, 0(a7)
	and t2, t4, t3
	and s6, t4, s5
	ld t4, 256(a7)
	and t5, t4, t3
	and s7, t4, s5
	ld t4, 512(a7)
	and t6, t4, t3
	and s8, t4, s5
	ld t4, 768(a7)
	and t0, t4, t3
	and s9, t4, s5
	slli t3, t1, 62
	srai t3, t3, 63
	slli s5, s4, 62
	srai s5, s5, 63
	ld t4, 8(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 264(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 520(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 776(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 61
	srai t3, t3, 63
	slli s5, s4, 61
	srai s5, s5, 63
	ld t4, 16(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 272(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 528(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 784(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 60
	srai t3, t3, 63
	slli s5, s4, 60
	srai s5, s5, 63
	ld t4, 24(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 280(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 536(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 792(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 59
	srai t3, t3, 63
	slli s5, s4, 59
	srai s5, s5, 63
	ld t4, 32(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 288(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 544(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 800(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 58
	srai t3, t3, 63
	slli s5, s4, 58
	srai s5, s5, 63
	ld t4, 40(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 296(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 552(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 808(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 57
	srai t3, t3, 63
	slli s5, s4, 57
	srai s5, s5, 63
	ld t4, 48(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 304(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 560(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 816(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 56
	srai t3, t3, 63
	slli s5, s4, 56
	srai s5, s5, 63
	ld t4, 56(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 312(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 568(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 824(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 55
	srai t3, t3, 63
	slli s5, s4, 55
	srai s5, s5, 63
	ld t4, 64(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 320(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 576(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 832(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 54
	srai t3, t3, 63
	slli s5, s4, 54
	srai s5, s5, 63
	ld t4, 72(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 328(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 584(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 840(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 53
	srai t3, t3, 63
	slli s5, s4, 53
	srai s5, s5, 63
	ld t4, 80(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 336(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 592(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 848(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 52
	srai t3, t3, 63
	slli s5, s4, 52
	srai s5, s5, 63
	ld t4, 88(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 344(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 600(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 856(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 51
	srai t3, t3, 63
	slli s5, s4, 51
	srai s5, s5, 63
	ld t4, 96(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 352(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 608(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 864(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 50
	srai t3, t3, 63
	slli s5, s4, 50
	srai s5, s5, 63
	ld t4, 104(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 360(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 616(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 872(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 49
	srai t3, t3, 63
	slli s5, s4, 49
	srai s5, s5, 63
	ld t4, 112(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 368(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 624(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 880(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 48
	srai t3, t3, 63
	slli s5, s4, 48
	srai s5, s5, 63
	ld t4, 120(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 376(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 632(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 888(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 47
	srai t3, t3, 63
	slli s5, s4, 47
	srai s5, s5, 63
	ld t4, 128(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 384(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 640(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 896(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 46
	srai t3, t3, 63
	slli s5, s4, 46
	srai s5, s5, 63
	ld t4, 136(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 392(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 648(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 904(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 45
	srai t3, t3, 63
	slli s5, s4, 45
	srai s5, s5, 63
	ld t4, 144(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 400(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 656(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 912(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 44
	srai t3, t3, 63
	slli s5, s4, 44
	srai s5, s5, 63
	ld t4, 152(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 408(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 664(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 920(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 43
	srai t3, t3, 63
	slli s5, s4, 43
	srai s5, s5, 63
	ld t4, 160(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 416(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 672(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 928(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 42
	srai t3, t3, 63
	slli s5, s4, 42
	srai s5, s5, 63
	ld t4, 168(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 424(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 680(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 936(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 41
	srai t3, t3, 63
	slli s5, s4, 41
	srai s5, s5, 63
	ld t4, 176(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 432(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 688(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 944(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 40
	srai t3, t3, 63
	slli s5, s4, 40
	srai s5, s5, 63
	ld t4, 184(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 440(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 696(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 952(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 39
	srai t3, t3, 63
	slli s5, s4, 39
	srai s5, s5, 63
	ld t4, 192(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 448(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 704(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 960(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 38
	srai t3, t3, 63
	slli s5, s4, 38
	srai s5, s5, 63
	ld t4, 200(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 456(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 712(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 968(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 37
	srai t3, t3, 63
	slli s5, s4, 37
	srai s5, s5, 63
	ld t4, 208(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 464(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 720(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 976(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 36
	srai t3, t3, 63
	slli s5, s4, 36
	srai s5, s5, 63
	ld t4, 216(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 472(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 728(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 984(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 35
	srai t3, t3, 63
	slli s5, s4, 35
	srai s5, s5, 63
	ld t4, 224(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 480(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 736(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 992(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 34
	srai t3, t3, 63
	slli s5, s4, 34
	srai s5, s5, 63
	ld t4, 232(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 488(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 744(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1000(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 33
	srai t3, t3, 63
	slli s5, s4, 33
	srai s5, s5, 63
	ld t4, 240(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 496(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 752(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1008(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 32
	srai t3, t3, 63
	slli s5, s4, 32
	srai s5, s5, 63
	ld t4, 248(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 504(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 760(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1016(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	srli t3, a3, 16
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	srli s5, s1, 16
	andi s5, s5, 7
	slli s5, s5, 3
	srl s6, s6, s5
	andi s6, s6, 255
	srl s7, s7, s5
	andi s7, s7, 255
	slli s7, s7, 8
	srl s8, s8, s5
	andi s8, s8, 255
	slli s8, s8, 16
	srl s9, s9, s5
	andi s9, s9, 255
	slli s9, s9, 24
	or s6, s6, s7
	or s8, s8, s9
	or s6, s6, s8
	add a5, a5, t2
	add s3, s3, s6
	addi a7, a7, 1024
	slli t1, a3, 48
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli s4, s1, 48
	srli s4, s4, 59
	addi s5, zero, 1
	sll s4, s5, s4
	slli t3, t1, 63
	srai t3, t3, 63
	slli s5, s4, 63
	srai s5, s5, 63
	ld t4, 0(a7)
	and t2, t4, t3
	and s6, t4, s5
	ld t4, 256(a7)
	and t5, t4, t3
	and s7, t4, s5
	ld t4, 512(a7)
	and t6, t4, t3
	and s8, t4, s5
	ld t4, 768(a7)
	and t0, t4, t3
	and s9, t4, s5
	slli t3, t1, 62
	srai t3, t3, 63
	slli s5, s4, 62
	srai s5, s5, 63
	ld t4, 8(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 264(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 520(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 776(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 61
	srai t3, t3, 63
	slli s5, s4, 61
	srai s5, s5, 63
	ld t4, 16(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 272(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 528(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 784(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 60
	srai t3, t3, 63
	slli s5, s4, 60
	srai s5, s5, 63
	ld t4, 24(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 280(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 536(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 792(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 59
	srai t3, t3, 63
	slli s5, s4, 59
	srai s5, s5, 63
	ld t4, 32(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 288(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 544(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 800(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 58
	srai t3, t3, 63
	slli s5, s4, 58
	srai s5, s5, 63
	ld t4, 40(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 296(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 552(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 808(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 57
	srai t3, t3, 63
	slli s5, s4, 57
	srai s5, s5, 63
	ld t4, 48(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 304(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 560(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 816(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 56
	srai t3, t3, 63
	slli s5, s4, 56
	srai s5, s5, 63
	ld t4, 56(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 312(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 568(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 824(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 55
	srai t3, t3, 63
	slli s5, s4, 55
	srai s5, s5, 63
	ld t4, 64(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 320(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 576(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 832(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 54
	srai t3, t3, 63
	slli s5, s4, 54
	srai s5, s5, 63
	ld t4, 72(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 328(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 584(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 840(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 53
	srai t3, t3, 63
	slli s5, s4, 53
	srai s5, s5, 63
	ld t4, 80(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 336(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 592(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 848(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 52
	srai t3, t3, 63
	slli s5, s4, 52
	srai s5, s5, 63
	ld t4, 88(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 344(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 600(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 856(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 51
	srai t3, t3, 63
	slli s5, s4, 51
	srai s5, s5, 63
	ld t4, 96(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 352(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 608(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 864(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 50
	srai t3, t3, 63
	slli s5, s4, 50
	srai s5, s5, 63
	ld t4, 104(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 360(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 616(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 872(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 49
	srai t3, t3, 63
	slli s5, s4, 49
	srai s5, s5, 63
	ld t4, 112(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 368(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 624(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 880(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 48
	srai t3, t3, 63
	slli s5, s4, 48
	srai s5, s5, 63
	ld t4, 120(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 376(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 632(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 888(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 47
	srai t3, t3, 63
	slli s5, s4, 47
	srai s5, s5, 63
	ld t4, 128(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 384(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 640(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 896(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 46
	srai t3, t3, 63
	slli s5, s4, 46
	srai s5, s5, 63
	ld t4, 136(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 392(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 648(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 904(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 45
	srai t3, t3, 63
	slli s5, s4, 45
	srai s5, s5, 63
	ld t4, 144(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 400(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 656(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 912(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 44
	srai t3, t3, 63
	slli s5, s4, 44
	srai s5, s5, 63
	ld t4, 152(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 408(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 664(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 920(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 43
	srai t3, t3, 63
	slli s5, s4, 43
	srai s5, s5, 63
	ld t4, 160(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 416(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 672(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 928(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 42
	srai t3, t3, 63
	slli s5, s4, 42
	srai s5, s5, 63
	ld t4, 168(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 424(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 680(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 936(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 41
	srai t3, t3, 63
	slli s5, s4, 41
	srai s5, s5, 63
	ld t4, 176(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 432(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 688(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 944(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 40
	srai t3, t3, 63
	slli s5, s4, 40
	srai s5, s5, 63
	ld t4, 184(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 440(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 696(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 952(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 39
	srai t3, t3, 63
	slli s5, s4, 39
	srai s5, s5, 63
	ld t4, 192(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 448(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 704(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 960(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 38
	srai t3, t3, 63
	slli s5, s4, 38
	srai s5, s5, 63
	ld t4, 200(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 456(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 712(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 968(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 37
	srai t3, t3, 63
	slli s5, s4, 37
	srai s5, s5, 63
	ld t4, 208(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 464(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 720(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 976(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 36
	srai t3, t3, 63
	slli s5, s4, 36
	srai s5, s5, 63
	ld t4, 216(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 472(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 728(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 984(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 35
	srai t3, t3, 63
	slli s5, s4, 35
	srai s5, s5, 63
	ld t4, 224(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 480(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 736(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 992(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 34
	srai t3, t3, 63
	slli s5, s4, 34
	srai s5, s5, 63
	ld t4, 232(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 488(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 744(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1000(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 33
	srai t3, t3, 63
	slli s5, s4, 33
	srai s5, s5, 63
	ld t4, 240(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 496(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 752(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1008(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 32
	srai t3, t3, 63
	slli s5, s4, 32
	srai s5, s5, 63
	ld t4, 248(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 504(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 760(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1016(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	srli t3, a3, 8
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	srli s5, s1, 8
	andi s5, s5, 7
	slli s5, s5, 3
	srl s6, s6, s5
	andi s6, s6, 255
	srl s7, s7, s5
	andi s7, s7, 255
	slli s7, s7, 8
	srl s8, s8, s5
	andi s8, s8, 255
	slli s8, s8, 16
	srl s9, s9, s5
	andi s9, s9, 255
	slli s9, s9, 24
	or s6, s6, s7
	or s8, s8, s9
	or s6, s6, s8
	xor a5, a5, t2
	xor s3, s3, s6
	addi a7, a7, 1024
	slli t1, a3, 56
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli s4, s1, 56
	srli s4, s4, 59
	addi s5, zero, 1
	sll s4, s5, s4
	slli t3, t1, 63
	srai t3, t3, 63
	slli s5, s4, 63
	srai s5, s5, 63
	ld t4, 0(a7)
	and t2, t4, t3
	and s6, t4, s5
	ld t4, 256(a7)
	and t5, t4, t3
	and s7, t4, s5
	ld t4, 512(a7)
	and t6, t4, t3
	and s8, t4, s5
	ld t4, 768(a7)
	and t0, t4, t3
	and s9, t4, s5
	slli t3, t1, 62
	srai t3, t3, 63
	slli s5, s4, 62
	srai s5, s5, 63
	ld t4, 8(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 264(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 520(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 776(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 61
	srai t3, t3, 63
	slli s5, s4, 61
	srai s5, s5, 63
	ld t4, 16(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 272(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 528(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 784(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 60
	srai t3, t3, 63
	slli s5, s4, 60
	srai s5, s5, 63
	ld t4, 24(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 280(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 536(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 792(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 59
	srai t3, t3, 63
	slli s5, s4, 59
	srai s5, s5, 63
	ld t4, 32(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 288(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 544(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 800(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 58
	srai t3, t3, 63
	slli s5, s4, 58
	srai s5, s5, 63
	ld t4, 40(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 296(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 552(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 808(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 57
	srai t3, t3, 63
	slli s5, s4, 57
	srai s5, s5, 63
	ld t4, 48(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 304(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 560(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 816(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 56
	srai t3, t3, 63
	slli s5, s4, 56
	srai s5, s5, 63
	ld t4, 56(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 312(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 568(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 824(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 55
	srai t3, t3, 63
	slli s5, s4, 55
	srai s5, s5, 63
	ld t4, 64(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 320(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 576(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 832(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 54
	srai t3, t3, 63
	slli s5, s4, 54
	srai s5, s5, 63
	ld t4, 72(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 328(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 584(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 840(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 53
	srai t3, t3, 63
	slli s5, s4, 53
	srai s5, s5, 63
	ld t4, 80(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 336(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 592(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 848(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 52
	srai t3, t3, 63
	slli s5, s4, 52
	srai s5, s5, 63
	ld t4, 88(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 344(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 600(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 856(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 51
	srai t3, t3, 63
	slli s5, s4, 51
	srai s5, s5, 63
	ld t4, 96(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 352(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 608(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 864(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 50
	srai t3, t3, 63
	slli s5, s4, 50
	srai s5, s5, 63
	ld t4, 104(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 360(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 616(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 872(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 49
	srai t3, t3, 63
	slli s5, s4, 49
	srai s5, s5, 63
	ld t4, 112(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 368(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 624(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 880(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 48
	srai t3, t3, 63
	slli s5, s4, 48
	srai s5, s5, 63
	ld t4, 120(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 376(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 632(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 888(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 47
	srai t3, t3, 63
	slli s5, s4, 47
	srai s5, s5, 63
	ld t4, 128(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 384(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 640(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 896(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 46
	srai t3, t3, 63
	slli s5, s4, 46
	srai s5, s5, 63
	ld t4, 136(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 392(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 648(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 904(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 45
	srai t3, t3, 63
	slli s5, s4, 45
	srai s5, s5, 63
	ld t4, 144(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 400(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 656(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 912(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 44
	srai t3, t3, 63
	slli s5, s4, 44
	srai s5, s5, 63
	ld t4, 152(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 408(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 664(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 920(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 43
	srai t3, t3, 63
	slli s5, s4, 43
	srai s5, s5, 63
	ld t4, 160(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 416(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 672(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 928(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 42
	srai t3, t3, 63
	slli s5, s4, 42
	srai s5, s5, 63
	ld t4, 168(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 424(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 680(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 936(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 41
	srai t3, t3, 63
	slli s5, s4, 41
	srai s5, s5, 63
	ld t4, 176(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 432(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 688(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 944(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 40
	srai t3, t3, 63
	slli s5, s4, 40
	srai s5, s5, 63
	ld t4, 184(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 440(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 696(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 952(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 39
	srai t3, t3, 63
	slli s5, s4, 39
	srai s5, s5, 63
	ld t4, 192(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 448(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 704(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 960(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 38
	srai t3, t3, 63
	slli s5, s4, 38
	srai s5, s5, 63
	ld t4, 200(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 456(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 712(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 968(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 37
	srai t3, t3, 63
	slli s5, s4, 37
	srai s5, s5, 63
	ld t4, 208(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 464(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 720(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 976(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 36
	srai t3, t3, 63
	slli s5, s4, 36
	srai s5, s5, 63
	ld t4, 216(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 472(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 728(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 984(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 35
	srai t3, t3, 63
	slli s5, s4, 35
	srai s5, s5, 63
	ld t4, 224(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 480(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 736(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 992(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 34
	srai t3, t3, 63
	slli s5, s4, 34
	srai s5, s5, 63
	ld t4, 232(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 488(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 744(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1000(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 33
	srai t3, t3, 63
	slli s5, s4, 33
	srai s5, s5, 63
	ld t4, 240(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 496(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 752(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1008(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	slli t3, t1, 32
	srai t3, t3, 63
	slli s5, s4, 32
	srai s5, s5, 63
	ld t4, 248(a7)
	and s10, t4, t3
	or t2, t2, s10
	and t4, t4, s5
	or s6, s6, t4
	ld t4, 504(a7)
	and s10, t4, t3
	or t5, t5, s10
	and t4, t4, s5
	or s7, s7, t4
	ld t4, 760(a7)
	and s10, t4, t3
	or t6, t6, s10
	and t4, t4, s5
	or s8, s8, t4
	ld t4, 1016(a7)
	and s10, t4, t3
	or t0, t0, s10
	and t4, t4, s5
	or s9, s9, t4
	srli t3, a3, 0
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	srli s5, s1, 0
	andi s5, s5, 7
	slli s5, s5, 3
	srl s6, s6, s5
	andi s6, s6, 255
	srl s7, s7, s5
	andi s7, s7, 255
	slli s7, s7, 8
	srl s8, s8, s5
	andi s8, s8, 255
	slli s8, s8, 16
	srl s9, s9, s5
	andi s9, s9, 255
	slli s9, s9, 24
	or s6, s6, s7
	or s8, s8, s9
	or s6, s6, s8
	add a5, a5, t2
	add s3, s3, s6
	addi a7, a7, -2048
	addi a7, a7, -1024
	xor a4, a4, a5
	or t4, a3, a3
	or a3, a4, a4
	or a4, t4, t4
	xor s2, s2, s3
	or t4, s1, s1
	or s1, s2, s2
	or s2, t4, t4
	addi a6, a6, 4
	sub t4, a6, a7
	addi t4, t4, -2047
	addi t4, t4, -2047
	addi t4, t4, -66
	bnez t4, 20b
	lwu t4, 0(a6)
	xor a5, a3, t4
	xor s3, s1, t4
	lwu t4, 4(a6)
	xor a3, t4, a4
	xor s1, t4, s2
	or a4, a5, a5
	or s2, s3, s3
	srli t4, a3, 24
	sb t4, 0(a1)
	srli t4, a3, 16
	sb t4, 1(a1)
	srli t4, a3, 8
	sb t4, 2(a1)
	srli t4, a3, 0
	sb t4, 3(a1)
	srli t4, a4, 24
	sb t4, 4(a1)
	srli t4, a4, 16
	sb t4, 5(a1)
	srli t4, a4, 8
	sb t4, 6(a1)
	srli t4, a4, 0
	sb t4, 7(a1)
	srli t4, s1, 24
	sb t4, 8(a1)
	srli t4, s1, 16
	sb t4, 9(a1)
	srli t4, s1, 8
	sb t4, 10(a1)
	srli t4, s1, 0
	sb t4, 11(a1)
	srli t4, s2, 24
	sb t4, 12(a1)
	srli t4, s2, 16
	sb t4, 13(a1)
	srli t4, s2, 8
	sb t4, 14(a1)
	srli t4, s2, 0
	sb t4, 15(a1)
	addi a1, a1, 16
	addi a2, a2, -2
	addi s1, s0, 0
	addi s2, s11, 0
	addi s3, ra, 0
	addi s4, a7, -64
	addi t0, a7, 2047
	addi t0, t0, 2047
	addi t0, t0, 74
	ld s0, 0(t0)
	ld s5, 8(t0)
	ld s6, 16(t0)
	ld s7, 24(t0)
	ld s8, 32(t0)
	ld s9, 40(t0)
	ld s10, 48(t0)
	ld s11, 56(t0)
	ld ra, 64(t0)
	ret
	.option pop
