// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	add x4, x1, #0
	movz x15, #1023, lsl #0
	movk x15, #0, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #64, lsl #0
20:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	ldrb w10, [x0, #1]
	lsl x10, x10, #8
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #10
	lsl x10, x10, #13
	str w10, [x4, #0]
	ldrb w10, [x0, #2]
	lsl x10, x10, #6
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #10
	lsl x10, x10, #13
	str w10, [x4, #4]
	ldrb w10, [x0, #3]
	lsl x10, x10, #4
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #10
	lsl x10, x10, #13
	str w10, [x4, #8]
	ldrb w10, [x0, #4]
	lsl x10, x10, #2
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #10
	lsl x10, x10, #13
	str w10, [x4, #12]
	add x0, x0, #5
	add x4, x4, #16
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6
