// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 128
20:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [esi+1]
	movzx edx, BYTE PTR [esi+2]
	mov ebp, ebx
	shr ebp, 4
	ror edx, 28
	add ebp, edx
	and ebx, 15
	ror ebx, 24
	add eax, ebx
	sub eax, 3329
	sbb edx, edx
	and edx, 3329
	add eax, edx
	mov DWORD PTR [edi], eax
	sub ebp, 3329
	sbb edx, edx
	and edx, 3329
	add ebp, edx
	mov DWORD PTR [edi+4], ebp
	add esi, 3
	add edi, 8
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
