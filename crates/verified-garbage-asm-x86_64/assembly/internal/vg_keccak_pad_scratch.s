// The functions of `src/internal/vg_keccak_pad_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad_scratch:
	movzx eax, BYTE PTR [rdi+rdx*1]
	xor rax, rcx
	mov BYTE PTR [rdi+rdx*1], al
	movzx eax, BYTE PTR [rdi+rsi*1-1]
	xor rax, 128
	mov BYTE PTR [rdi+rsi*1-1], al
	mov rsi, r8
	call {vg_keccak_f1600}
	ret
	.p2align 6
