// The functions of `src/internal/vg_mldsa87_verify_prepared_entry_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_verify_prepared_entry_umaal:
	push {r4, lr}
	mov r4, lr
	movw r12, #2592
	movt r12, #0
	add r12, r0, r12
	push {r12, lr}
	bl {vg_mldsa87_verify_with_cache_umaal}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr
