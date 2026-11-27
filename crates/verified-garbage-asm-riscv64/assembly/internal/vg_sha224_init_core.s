// The functions of `src/internal/vg_sha224_init_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init_core:
	.option push
	.option arch, +m, +c
	lui t0, 790618
	addiw t0, t0, -296
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	lui t0, 223181
	addiw t0, t0, 1287
	sb t0, 4(a0)
	srli t1, t0, 8
	sb t1, 5(a0)
	srli t1, t0, 16
	sb t1, 6(a0)
	srli t1, t0, 24
	sb t1, 7(a0)
	lui t0, 198414
	addiw t0, t0, -745
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	lui t0, 1011942
	addiw t0, t0, -1735
	sb t0, 12(a0)
	srli t1, t0, 8
	sb t1, 13(a0)
	srli t1, t0, 16
	sb t1, 14(a0)
	srli t1, t0, 24
	sb t1, 15(a0)
	lui t0, 1047553
	addiw t0, t0, -1231
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	lui t0, 427393
	addiw t0, t0, 1297
	sb t0, 20(a0)
	srli t1, t0, 8
	sb t1, 21(a0)
	srli t1, t0, 16
	sb t1, 22(a0)
	srli t1, t0, 24
	sb t1, 23(a0)
	lui t0, 413593
	addiw t0, t0, -89
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	lui t0, 782245
	addiw t0, t0, -92
	sb t0, 28(a0)
	srli t1, t0, 8
	sb t1, 29(a0)
	srli t1, t0, 16
	sb t1, 30(a0)
	srli t1, t0, 24
	sb t1, 31(a0)
	ret
	.option pop
