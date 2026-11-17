// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	str r4, [r1, #396]
	str r5, [r1, #400]
	str r6, [r1, #404]
	str r7, [r1, #408]
	str r8, [r1, #412]
	str r9, [r1, #416]
	str r10, [r1, #420]
	str r11, [r1, #424]
	str lr, [r1, #428]
	bl {vg_keccak_f1600_enter}
	bl {vg_keccak_f1600_rounds}
	bl {vg_keccak_f1600_leave}
	ldr r4, [r1, #396]
	ldr r5, [r1, #400]
	ldr r6, [r1, #404]
	ldr r7, [r1, #408]
	ldr r8, [r1, #412]
	ldr r9, [r1, #416]
	ldr r10, [r1, #420]
	ldr r11, [r1, #424]
	ldr lr, [r1, #428]
	bx lr
