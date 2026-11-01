// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	ldr r12, [sp, #0]
	push {r4, r5, r6, r7}
	sub r6, r1, r2
	mov r4, r12
	mov r12, #0
	mov r5, r3
20:
	str r12, [r5, #0]
	add r5, r5, #4
	subs r4, r4, #1
	bne 20b
	mov r1, #0
	add r5, r0, r2
21:
	sub r7, r2, r1
	lsr r7, r7, #31
	cmp r7, #0
	beq 22f
	b 23f
22:
	ldrb r4, [r5, #0]
	sub r7, r4, r1
	lsr r7, r7, #31
	cmp r7, #0
	beq 24f
	mov r1, #256
	b 25f
24:
	sub r7, r2, r4
	lsr r7, r7, #31
	cmp r7, #0
	beq 26f
	mov r1, #256
	b 27f
26:
	sub r7, r1, r4
	lsr r7, r7, #31
	cmp r7, #0
	beq 28f
	add r12, r0, r1
	ldrb r12, [r12, #0]
	add r12, r3, r12, lsl #2
	mov r7, #1
	str r7, [r12, #0]
	add r1, r1, #1
	sub r7, r1, r4
	lsr r7, r7, #31
	cmp r7, #0
	beq 210f
212:
	add r12, r0, r1
	ldrb r7, [r12, #0]
	sub r12, r12, #1
	ldrb r12, [r12, #0]
	sub r7, r12, r7
	lsr r7, r7, #31
	cmp r7, #0
	beq 213f
	add r12, r0, r1
	ldrb r12, [r12, #0]
	add r12, r3, r12, lsl #2
	mov r7, #1
	str r7, [r12, #0]
	add r1, r1, #1
	b 214f
213:
	mov r1, #256
214:
	sub r7, r1, r4
	lsr r7, r7, #31
	cmp r7, #0
	bne 212b
	b 211f
210:
211:
	b 29f
28:
29:
27:
25:
23:
	add r5, r5, #1
	add r3, r3, #1024
	subs r6, r6, #1
	bne 21b
	sub r7, r1, r2
	lsr r7, r7, #31
	cmp r7, #0
	beq 215f
217:
	add r12, r0, r1
	ldrb r12, [r12, #0]
	cmp r12, #0
	beq 218f
	mov r1, #256
	b 219f
218:
	add r1, r1, #1
219:
	sub r7, r1, r2
	lsr r7, r7, #31
	cmp r7, #0
	bne 217b
	b 216f
215:
216:
	sub r7, r2, r1
	lsr r7, r7, #31
	mov r0, #1
	sub r0, r0, r7
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr r7, [sp, #12]
	ldr r4, [sp], #16
	bx lr
