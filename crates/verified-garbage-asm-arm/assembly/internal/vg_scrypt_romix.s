// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	ldr r12, [sp, #0]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r7, [r12, #136]
	str r8, [r12, #140]
	str r9, [r12, #144]
	str lr, [r12, #148]
	str r6, [r12, #152]
	mov r4, r0
	mov r5, r2
	mov r6, r12
	lsl r7, r1, #7
	mov r0, r1
	mov r1, #1
	add r2, r3, r3
20:
	add r0, r0, r0
	add r1, r1, r1
	cmp r0, r2
	bne 20b
	lsr r1, r1, #1
	str r1, [r6, #156]
	mov r8, r1
	mov r9, r5
21:
	mov r0, r4
	mov r1, r9
	lsr r2, r7, #2
22:
	ldr r3, [r0, #0]
	str r3, [r1, #0]
	add r0, r0, #4
	add r1, r1, #4
	subs r2, r2, #1
	bne 22b
	mov r0, r9
	lsr r1, r7, #7
	mov r2, r4
	mov r3, r1
	bl {vg_scrypt_blockmix}
	add r9, r9, r7
	subs r8, r8, #1
	bne 21b
	ldr r8, [r6, #156]
	sub r9, r8, #1
23:
	add r0, r4, r7
	sub r0, r0, #64
	ldr r0, [r0, #0]
	and r0, r0, r9
	mov r1, r5
	mov r2, r7
24:
	and r3, r0, #1
	cmp r3, #0
	bne 25f
	b 26f
25:
	add r1, r1, r2
26:
	add r2, r2, r2
	lsr r0, r0, #1
	cmp r0, #0
	bne 24b
	mov r0, r4
	add r2, r6, #192
	lsr r3, r7, #2
27:
	ldr r12, [r0, #0]
	ldr lr, [r1, #0]
	eor r12, r12, lr
	str r12, [r2, #0]
	add r0, r0, #4
	add r1, r1, #4
	add r2, r2, #4
	subs r3, r3, #1
	bne 27b
	add r0, r6, #192
	lsr r1, r7, #7
	mov r2, r4
	mov r3, r1
	bl {vg_scrypt_blockmix}
	subs r8, r8, #1
	bne 23b
	ldr r4, [r6, #128]
	ldr r5, [r6, #132]
	ldr r7, [r6, #136]
	ldr r8, [r6, #140]
	ldr r9, [r6, #144]
	ldr lr, [r6, #148]
	ldr r6, [r6, #152]
	bx lr
