// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	ldr r12, [sp, #0]
	push {r4, r5}
	sub r1, r12, r2
	mov r4, r12
	mov r12, #0
	mov r5, r3
20:
	strb r12, [r5, #0]
	add r5, r5, #1
	subs r4, r4, #1
	bne 20b
	mov r4, r1
	add r5, r3, r2
	mov r1, #0
21:
	mov r12, #0
22:
	ldr r2, [r0, #0]
	cmp r2, #0
	beq 23f
	add r2, r3, r1
	strb r12, [r2, #0]
	add r1, r1, #1
	b 24f
23:
24:
	add r0, r0, #4
	add r12, r12, #1
	cmp r12, #256
	bne 22b
	strb r1, [r5, #0]
	add r5, r5, #1
	subs r4, r4, #1
	bne 21b
	ldr r5, [sp, #4]
	ldr r4, [sp], #8
	bx lr
