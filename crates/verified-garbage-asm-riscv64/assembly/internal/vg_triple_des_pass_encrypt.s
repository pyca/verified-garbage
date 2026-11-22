// The functions of `src/internal/vg_triple_des_pass_encrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_pass_encrypt:
	.option push
	.option arch, +m, +c
	addi a4, zero, 8
20:
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 20b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	ret
	.option pop
