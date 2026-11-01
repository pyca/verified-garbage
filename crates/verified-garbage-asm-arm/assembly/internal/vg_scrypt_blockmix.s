// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	ldr r12, [sp, #0]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r8, [r12, #76]
	str r9, [r12, #80]
	str lr, [r12, #84]
	str r7, [r12, #88]
	mov r8, r1
	mov r4, r0
	mov r5, r2
	mov r7, r12
	add r6, r2, r1, lsl #6
	add r9, r0, r1, lsl #7
	sub r9, r9, #64
20:
	ldr r2, [r9, #0]
	ldr r3, [r4, #0]
	eor r2, r2, r3
	str r2, [r5, #0]
	ldr r2, [r9, #4]
	ldr r3, [r4, #4]
	eor r2, r2, r3
	str r2, [r5, #4]
	ldr r2, [r9, #8]
	ldr r3, [r4, #8]
	eor r2, r2, r3
	str r2, [r5, #8]
	ldr r2, [r9, #12]
	ldr r3, [r4, #12]
	eor r2, r2, r3
	str r2, [r5, #12]
	ldr r2, [r9, #16]
	ldr r3, [r4, #16]
	eor r2, r2, r3
	str r2, [r5, #16]
	ldr r2, [r9, #20]
	ldr r3, [r4, #20]
	eor r2, r2, r3
	str r2, [r5, #20]
	ldr r2, [r9, #24]
	ldr r3, [r4, #24]
	eor r2, r2, r3
	str r2, [r5, #24]
	ldr r2, [r9, #28]
	ldr r3, [r4, #28]
	eor r2, r2, r3
	str r2, [r5, #28]
	ldr r2, [r9, #32]
	ldr r3, [r4, #32]
	eor r2, r2, r3
	str r2, [r5, #32]
	ldr r2, [r9, #36]
	ldr r3, [r4, #36]
	eor r2, r2, r3
	str r2, [r5, #36]
	ldr r2, [r9, #40]
	ldr r3, [r4, #40]
	eor r2, r2, r3
	str r2, [r5, #40]
	ldr r2, [r9, #44]
	ldr r3, [r4, #44]
	eor r2, r2, r3
	str r2, [r5, #44]
	ldr r2, [r9, #48]
	ldr r3, [r4, #48]
	eor r2, r2, r3
	str r2, [r5, #48]
	ldr r2, [r9, #52]
	ldr r3, [r4, #52]
	eor r2, r2, r3
	str r2, [r5, #52]
	ldr r2, [r9, #56]
	ldr r3, [r4, #56]
	eor r2, r2, r3
	str r2, [r5, #56]
	ldr r2, [r9, #60]
	ldr r3, [r4, #60]
	eor r2, r2, r3
	str r2, [r5, #60]
	mov r0, r5
	mov r1, r7
	bl {vg_salsa20_8}
	add r4, r4, #64
	ldr r2, [r5, #0]
	ldr r3, [r4, #0]
	eor r2, r2, r3
	str r2, [r6, #0]
	ldr r2, [r5, #4]
	ldr r3, [r4, #4]
	eor r2, r2, r3
	str r2, [r6, #4]
	ldr r2, [r5, #8]
	ldr r3, [r4, #8]
	eor r2, r2, r3
	str r2, [r6, #8]
	ldr r2, [r5, #12]
	ldr r3, [r4, #12]
	eor r2, r2, r3
	str r2, [r6, #12]
	ldr r2, [r5, #16]
	ldr r3, [r4, #16]
	eor r2, r2, r3
	str r2, [r6, #16]
	ldr r2, [r5, #20]
	ldr r3, [r4, #20]
	eor r2, r2, r3
	str r2, [r6, #20]
	ldr r2, [r5, #24]
	ldr r3, [r4, #24]
	eor r2, r2, r3
	str r2, [r6, #24]
	ldr r2, [r5, #28]
	ldr r3, [r4, #28]
	eor r2, r2, r3
	str r2, [r6, #28]
	ldr r2, [r5, #32]
	ldr r3, [r4, #32]
	eor r2, r2, r3
	str r2, [r6, #32]
	ldr r2, [r5, #36]
	ldr r3, [r4, #36]
	eor r2, r2, r3
	str r2, [r6, #36]
	ldr r2, [r5, #40]
	ldr r3, [r4, #40]
	eor r2, r2, r3
	str r2, [r6, #40]
	ldr r2, [r5, #44]
	ldr r3, [r4, #44]
	eor r2, r2, r3
	str r2, [r6, #44]
	ldr r2, [r5, #48]
	ldr r3, [r4, #48]
	eor r2, r2, r3
	str r2, [r6, #48]
	ldr r2, [r5, #52]
	ldr r3, [r4, #52]
	eor r2, r2, r3
	str r2, [r6, #52]
	ldr r2, [r5, #56]
	ldr r3, [r4, #56]
	eor r2, r2, r3
	str r2, [r6, #56]
	ldr r2, [r5, #60]
	ldr r3, [r4, #60]
	eor r2, r2, r3
	str r2, [r6, #60]
	mov r0, r6
	mov r1, r7
	bl {vg_salsa20_8}
	mov r9, r6
	add r4, r4, #64
	add r5, r5, #64
	add r6, r6, #64
	subs r8, r8, #1
	bne 20b
	ldr r4, [r7, #64]
	ldr r5, [r7, #68]
	ldr r6, [r7, #72]
	ldr r8, [r7, #76]
	ldr r9, [r7, #80]
	ldr lr, [r7, #84]
	ldr r7, [r7, #88]
	bx lr
