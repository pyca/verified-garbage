// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	mov r2, #128
20:
	ldr r3, [r0, #0]
	ldr r12, [r0, #4]
	strb r3, [r1, #0]
	lsr r3, r3, #8
	add r3, r3, r12, lsl #4
	strb r3, [r1, #1]
	lsr r12, r12, #4
	strb r12, [r1, #2]
	add r0, r0, #8
	add r1, r1, #3
	subs r2, r2, #1
	bne 20b
	bx lr
