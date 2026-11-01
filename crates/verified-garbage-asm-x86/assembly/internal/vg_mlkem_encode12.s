// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 128
20:
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	ror edx, 20
	add eax, edx
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	shr eax, 8
	mov BYTE PTR [edi+2], al
	add esi, 8
	add edi, 3
	sub ecx, 1
	jne 20b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
