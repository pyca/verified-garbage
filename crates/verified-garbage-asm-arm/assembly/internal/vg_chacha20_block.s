// The functions of `src/internal/vg_chacha20_block.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	str r4, [r1, #80]
	str r5, [r1, #84]
	str r6, [r1, #88]
	str r7, [r1, #92]
	str r8, [r1, #96]
	str r9, [r1, #100]
	str r10, [r1, #104]
	str r11, [r1, #108]
	str lr, [r1, #112]
	str r0, [r1, #116]
	ldr lr, [r0, #36]
	str lr, [r1, #68]
	ldr lr, [r0, #40]
	str lr, [r1, #72]
	ldr lr, [r0, #44]
	str lr, [r1, #76]
	ldr r2, [r0, #4]
	ldr r3, [r0, #8]
	ldr r4, [r0, #12]
	ldr r5, [r0, #16]
	ldr r6, [r0, #20]
	ldr r7, [r0, #24]
	ldr r8, [r0, #28]
	ldr lr, [r0, #32]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	ldr r11, [r0, #56]
	ldr r12, [r0, #60]
	ldr r0, [r0, #0]
	add r0, r0, r5
	eor r9, r0, r9
	add lr, lr, r9, ror #16
	eor r5, lr, r5
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6
	eor r10, r2, r10
	add lr, lr, r10, ror #16
	eor r6, lr, r6
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7
	eor r11, r3, r11
	add lr, lr, r11, ror #16
	eor r7, lr, r7
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8
	eor r12, r4, r12
	add lr, lr, r12, ror #16
	eor r8, lr, r8
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	add r0, r0, r5, ror #25
	eor r9, r0, r9, ror #24
	add lr, lr, r9, ror #16
	eor r5, lr, r5, ror #25
	add r0, r0, r5, ror #20
	eor r9, r0, r9, ror #16
	add lr, lr, r9, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #68]
	add r2, r2, r6, ror #25
	eor r10, r2, r10, ror #24
	add lr, lr, r10, ror #16
	eor r6, lr, r6, ror #25
	add r2, r2, r6, ror #20
	eor r10, r2, r10, ror #16
	add lr, lr, r10, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #72]
	add r3, r3, r7, ror #25
	eor r11, r3, r11, ror #24
	add lr, lr, r11, ror #16
	eor r7, lr, r7, ror #25
	add r3, r3, r7, ror #20
	eor r11, r3, r11, ror #16
	add lr, lr, r11, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #76]
	add r4, r4, r8, ror #25
	eor r12, r4, r12, ror #24
	add lr, lr, r12, ror #16
	eor r8, lr, r8, ror #25
	add r4, r4, r8, ror #20
	eor r12, r4, r12, ror #16
	add lr, lr, r12, ror #24
	eor r8, lr, r8, ror #20
	add r2, r2, r7, ror #25
	eor r9, r2, r9, ror #24
	add lr, lr, r9, ror #16
	eor r7, lr, r7, ror #25
	add r2, r2, r7, ror #20
	eor r9, r2, r9, ror #16
	add lr, lr, r9, ror #24
	eor r7, lr, r7, ror #20
	str lr, [r1, #76]
	ldr lr, [r1, #72]
	add r0, r0, r6, ror #25
	eor r12, r0, r12, ror #24
	add lr, lr, r12, ror #16
	eor r6, lr, r6, ror #25
	add r0, r0, r6, ror #20
	eor r12, r0, r12, ror #16
	add lr, lr, r12, ror #24
	eor r6, lr, r6, ror #20
	str lr, [r1, #72]
	ldr lr, [r1, #68]
	add r4, r4, r5, ror #25
	eor r11, r4, r11, ror #24
	add lr, lr, r11, ror #16
	eor r5, lr, r5, ror #25
	add r4, r4, r5, ror #20
	eor r11, r4, r11, ror #16
	add lr, lr, r11, ror #24
	eor r5, lr, r5, ror #20
	str lr, [r1, #68]
	ldr lr, [r1, #64]
	add r3, r3, r8, ror #25
	eor r10, r3, r10, ror #24
	add lr, lr, r10, ror #16
	eor r8, lr, r8, ror #25
	add r3, r3, r8, ror #20
	eor r10, r3, r10, ror #16
	add lr, lr, r10, ror #24
	eor r8, lr, r8, ror #20
	str lr, [r1, #64]
	ldr lr, [r1, #116]
	str r0, [r1, #0]
	ldr r0, [lr, #4]
	add r2, r0, r2
	str r2, [r1, #4]
	ldr r0, [lr, #8]
	add r3, r0, r3
	str r3, [r1, #8]
	ldr r0, [lr, #12]
	add r4, r0, r4
	str r4, [r1, #12]
	ldr r0, [lr, #16]
	add r5, r0, r5, ror #25
	str r5, [r1, #16]
	ldr r0, [lr, #20]
	add r6, r0, r6, ror #25
	str r6, [r1, #20]
	ldr r0, [lr, #24]
	add r7, r0, r7, ror #25
	str r7, [r1, #24]
	ldr r0, [lr, #28]
	add r8, r0, r8, ror #25
	str r8, [r1, #28]
	ldr r0, [lr, #48]
	add r9, r0, r9, ror #24
	str r9, [r1, #48]
	ldr r0, [lr, #52]
	add r10, r0, r10, ror #24
	str r10, [r1, #52]
	ldr r0, [lr, #56]
	add r11, r0, r11, ror #24
	str r11, [r1, #56]
	ldr r0, [lr, #60]
	add r12, r0, r12, ror #24
	str r12, [r1, #60]
	ldr r0, [lr, #0]
	ldr r2, [r1, #0]
	add r0, r2, r0
	str r0, [r1, #0]
	ldr r0, [lr, #32]
	ldr r2, [r1, #64]
	add r0, r2, r0
	str r0, [r1, #32]
	ldr r0, [lr, #36]
	ldr r2, [r1, #68]
	add r0, r2, r0
	str r0, [r1, #36]
	ldr r0, [lr, #40]
	ldr r2, [r1, #72]
	add r0, r2, r0
	str r0, [r1, #40]
	ldr r0, [lr, #44]
	ldr r2, [r1, #76]
	add r0, r2, r0
	str r0, [r1, #44]
	ldr r4, [r1, #80]
	ldr r5, [r1, #84]
	ldr r6, [r1, #88]
	ldr r7, [r1, #92]
	ldr r8, [r1, #96]
	ldr r9, [r1, #100]
	ldr r10, [r1, #104]
	ldr r11, [r1, #108]
	ldr lr, [r1, #112]
	bx lr
