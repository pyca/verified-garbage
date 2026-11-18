// The functions of `src/internal/vg_sha512_256_init_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_256_init_core:
	.option push
	.option arch, +m, +c
	lui t0, 140050
	addiw t0, t0, 405
	slli t0, t0, 32
	lui t1, 1032895
	addiw t1, t1, 1836
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 652630
	addiw t0, t0, -92
	slli t0, t0, 32
	lui t1, 820422
	addiw t1, t1, 1218
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 145724
	addiw t0, t0, -1941
	slli t0, t0, 32
	lui t1, 455995
	addiw t1, t1, 337
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 615303
	addiw t0, t0, 1817
	slli t0, t0, 32
	lui t1, 365583
	addiw t1, t1, -1347
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 615044
	addiw t0, t0, -285
	slli t0, t0, 32
	lui t1, 690416
	addiw t1, t1, -29
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 779746
	addiw t0, t0, -475
	slli t0, t0, 32
	lui t1, 342116
	addiw t1, t1, -1646
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 176154
	addiw t0, t0, -1540
	slli t0, t0, 32
	lui t1, 182364
	addiw t1, t1, -1878
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 60275
	addiw t0, t0, -547
	slli t0, t0, 32
	lui t1, 531539
	addiw t1, t1, -862
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop
