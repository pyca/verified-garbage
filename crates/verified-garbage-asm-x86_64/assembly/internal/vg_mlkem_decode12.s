// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	mov ecx, 128
20:
	movzx eax, BYTE PTR [rdi]
	movzx edx, BYTE PTR [rdi+1]
	ror edx, 24
	add eax, edx
	movzx edx, BYTE PTR [rdi+2]
	ror edx, 16
	add eax, edx
	mov edx, eax
	and eax, 4095
	shr edx, 12
	sub eax, 3329
	sbb r8d, r8d
	and r8d, 3329
	add eax, r8d
	sub edx, 3329
	sbb r8d, r8d
	and r8d, 3329
	add edx, r8d
	mov DWORD PTR [rsi], eax
	mov DWORD PTR [rsi+4], edx
	add rdi, 3
	add rsi, 8
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
