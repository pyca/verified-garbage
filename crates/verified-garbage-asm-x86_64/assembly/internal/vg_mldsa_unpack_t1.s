// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	mov ecx, 64
20:
	mov eax, DWORD PTR [rdi]
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 2
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+4], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 12
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+8], eax
	mov eax, DWORD PTR [rdi+1]
	shr eax, 22
	and eax, 1023
	ror eax, 19
	mov DWORD PTR [rsi+12], eax
	add rdi, 5
	add rsi, 16
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
