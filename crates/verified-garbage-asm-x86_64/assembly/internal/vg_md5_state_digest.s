// The functions of `src/internal/vg_md5_state_digest.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_state_digest:
	mov r8, rbx
	mov r9, rbp
	mov rbx, rdi
	mov rbp, rsi
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov rbx, r8
	mov rbp, r9
	ret
	.p2align 6
