// The functions of `src/internal/vg_triple_des_transpose.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_transpose:
	.option push
	.option arch, +m, +c
	addi a0, s0, 896
	ld s1, 0(a0)
	ld s2, 8(a0)
	ld s3, 16(a0)
	ld t0, 0(s0)
	ld t1, 64(s0)
	ld t2, 128(s0)
	ld t3, 192(s0)
	ld t4, 256(s0)
	ld t5, 320(s0)
	ld t6, 384(s0)
	ld a7, 448(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 64(s0)
	sd t2, 128(s0)
	sd t3, 192(s0)
	sd t4, 256(s0)
	sd t5, 320(s0)
	sd t6, 384(s0)
	sd a7, 448(s0)
	ld t0, 8(s0)
	ld t1, 72(s0)
	ld t2, 136(s0)
	ld t3, 200(s0)
	ld t4, 264(s0)
	ld t5, 328(s0)
	ld t6, 392(s0)
	ld a7, 456(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 8(s0)
	sd t1, 72(s0)
	sd t2, 136(s0)
	sd t3, 200(s0)
	sd t4, 264(s0)
	sd t5, 328(s0)
	sd t6, 392(s0)
	sd a7, 456(s0)
	ld t0, 16(s0)
	ld t1, 80(s0)
	ld t2, 144(s0)
	ld t3, 208(s0)
	ld t4, 272(s0)
	ld t5, 336(s0)
	ld t6, 400(s0)
	ld a7, 464(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 16(s0)
	sd t1, 80(s0)
	sd t2, 144(s0)
	sd t3, 208(s0)
	sd t4, 272(s0)
	sd t5, 336(s0)
	sd t6, 400(s0)
	sd a7, 464(s0)
	ld t0, 24(s0)
	ld t1, 88(s0)
	ld t2, 152(s0)
	ld t3, 216(s0)
	ld t4, 280(s0)
	ld t5, 344(s0)
	ld t6, 408(s0)
	ld a7, 472(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 24(s0)
	sd t1, 88(s0)
	sd t2, 152(s0)
	sd t3, 216(s0)
	sd t4, 280(s0)
	sd t5, 344(s0)
	sd t6, 408(s0)
	sd a7, 472(s0)
	ld t0, 32(s0)
	ld t1, 96(s0)
	ld t2, 160(s0)
	ld t3, 224(s0)
	ld t4, 288(s0)
	ld t5, 352(s0)
	ld t6, 416(s0)
	ld a7, 480(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 32(s0)
	sd t1, 96(s0)
	sd t2, 160(s0)
	sd t3, 224(s0)
	sd t4, 288(s0)
	sd t5, 352(s0)
	sd t6, 416(s0)
	sd a7, 480(s0)
	ld t0, 40(s0)
	ld t1, 104(s0)
	ld t2, 168(s0)
	ld t3, 232(s0)
	ld t4, 296(s0)
	ld t5, 360(s0)
	ld t6, 424(s0)
	ld a7, 488(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 40(s0)
	sd t1, 104(s0)
	sd t2, 168(s0)
	sd t3, 232(s0)
	sd t4, 296(s0)
	sd t5, 360(s0)
	sd t6, 424(s0)
	sd a7, 488(s0)
	ld t0, 48(s0)
	ld t1, 112(s0)
	ld t2, 176(s0)
	ld t3, 240(s0)
	ld t4, 304(s0)
	ld t5, 368(s0)
	ld t6, 432(s0)
	ld a7, 496(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 48(s0)
	sd t1, 112(s0)
	sd t2, 176(s0)
	sd t3, 240(s0)
	sd t4, 304(s0)
	sd t5, 368(s0)
	sd t6, 432(s0)
	sd a7, 496(s0)
	ld t0, 56(s0)
	ld t1, 120(s0)
	ld t2, 184(s0)
	ld t3, 248(s0)
	ld t4, 312(s0)
	ld t5, 376(s0)
	ld t6, 440(s0)
	ld a7, 504(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 56(s0)
	sd t1, 120(s0)
	sd t2, 184(s0)
	sd t3, 248(s0)
	sd t4, 312(s0)
	sd t5, 376(s0)
	sd t6, 440(s0)
	sd a7, 504(s0)
	ld s1, 24(a0)
	ld s2, 32(a0)
	ld s3, 40(a0)
	ld t0, 0(s0)
	ld t1, 8(s0)
	ld t2, 16(s0)
	ld t3, 24(s0)
	ld t4, 32(s0)
	ld t5, 40(s0)
	ld t6, 48(s0)
	ld a7, 56(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 8(s0)
	sd t2, 16(s0)
	sd t3, 24(s0)
	sd t4, 32(s0)
	sd t5, 40(s0)
	sd t6, 48(s0)
	sd a7, 56(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	ld t2, 80(s0)
	ld t3, 88(s0)
	ld t4, 96(s0)
	ld t5, 104(s0)
	ld t6, 112(s0)
	ld a7, 120(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 64(s0)
	sd t1, 72(s0)
	sd t2, 80(s0)
	sd t3, 88(s0)
	sd t4, 96(s0)
	sd t5, 104(s0)
	sd t6, 112(s0)
	sd a7, 120(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	ld t2, 144(s0)
	ld t3, 152(s0)
	ld t4, 160(s0)
	ld t5, 168(s0)
	ld t6, 176(s0)
	ld a7, 184(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 128(s0)
	sd t1, 136(s0)
	sd t2, 144(s0)
	sd t3, 152(s0)
	sd t4, 160(s0)
	sd t5, 168(s0)
	sd t6, 176(s0)
	sd a7, 184(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	ld t2, 208(s0)
	ld t3, 216(s0)
	ld t4, 224(s0)
	ld t5, 232(s0)
	ld t6, 240(s0)
	ld a7, 248(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 192(s0)
	sd t1, 200(s0)
	sd t2, 208(s0)
	sd t3, 216(s0)
	sd t4, 224(s0)
	sd t5, 232(s0)
	sd t6, 240(s0)
	sd a7, 248(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	ld t2, 272(s0)
	ld t3, 280(s0)
	ld t4, 288(s0)
	ld t5, 296(s0)
	ld t6, 304(s0)
	ld a7, 312(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 256(s0)
	sd t1, 264(s0)
	sd t2, 272(s0)
	sd t3, 280(s0)
	sd t4, 288(s0)
	sd t5, 296(s0)
	sd t6, 304(s0)
	sd a7, 312(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	ld t2, 336(s0)
	ld t3, 344(s0)
	ld t4, 352(s0)
	ld t5, 360(s0)
	ld t6, 368(s0)
	ld a7, 376(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 320(s0)
	sd t1, 328(s0)
	sd t2, 336(s0)
	sd t3, 344(s0)
	sd t4, 352(s0)
	sd t5, 360(s0)
	sd t6, 368(s0)
	sd a7, 376(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	ld t2, 400(s0)
	ld t3, 408(s0)
	ld t4, 416(s0)
	ld t5, 424(s0)
	ld t6, 432(s0)
	ld a7, 440(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 384(s0)
	sd t1, 392(s0)
	sd t2, 400(s0)
	sd t3, 408(s0)
	sd t4, 416(s0)
	sd t5, 424(s0)
	sd t6, 432(s0)
	sd a7, 440(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	ld t2, 464(s0)
	ld t3, 472(s0)
	ld t4, 480(s0)
	ld t5, 488(s0)
	ld t6, 496(s0)
	ld a7, 504(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 448(s0)
	sd t1, 456(s0)
	sd t2, 464(s0)
	sd t3, 472(s0)
	sd t4, 480(s0)
	sd t5, 488(s0)
	sd t6, 496(s0)
	sd a7, 504(s0)
	ret
	.option pop
