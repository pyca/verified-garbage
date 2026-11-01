// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	mov ecx, 128
20:
	mov eax, DWORD PTR [rdi]
	mov edx, DWORD PTR [rdi+4]
	ror edx, 20
	add eax, edx
	mov BYTE PTR [rsi], al
	shr eax, 8
	mov BYTE PTR [rsi+1], al
	shr eax, 8
	mov BYTE PTR [rsi+2], al
	add rdi, 8
	add rsi, 3
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
