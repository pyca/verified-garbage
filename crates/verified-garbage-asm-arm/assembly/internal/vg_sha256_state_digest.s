// The functions of `src/internal/vg_sha256_state_digest.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_state_digest:
	mov r2, r6
	mov r3, r9
	mov r12, r10
	mov r6, r1
	ldr r9, [r0, #0]
	rev r9, r9
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	rev r9, r9
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	rev r9, r9
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	rev r9, r9
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	rev r9, r9
	str r9, [r6, #16]
	ldr r9, [r0, #20]
	rev r9, r9
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	rev r9, r9
	str r9, [r6, #24]
	ldr r9, [r0, #28]
	rev r9, r9
	str r9, [r6, #28]
	mov r6, r2
	mov r9, r3
	mov r10, r12
	bx lr
