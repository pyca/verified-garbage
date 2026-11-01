// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	mov esi, esi
	mov r9, -1
	mov ecx, 256
20:
	mov eax, DWORD PTR [rdi+rcx*4-4]
	mov edx, 8380417
	sub rdx, rax
	sub rax, rsi
	sub rdx, rsi
	or rax, rdx
	and r9, rax
	sub rcx, 1
	jne 20b
	mov rax, r9
	shr rax, 63
	ret
	.p2align 6
