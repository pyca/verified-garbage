// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 64
20:
	mov ebx, 0
	movzx eax, BYTE PTR [esi]
	add ebx, eax
	movzx eax, BYTE PTR [esi+1]
	ror eax, 24
	add ebx, eax
	mov eax, ebx
	and eax, 1023
	shr ebx, 10
	ror eax, 19
	mov DWORD PTR [edi], eax
	movzx eax, BYTE PTR [esi+2]
	ror eax, 26
	add ebx, eax
	mov eax, ebx
	and eax, 1023
	shr ebx, 10
	ror eax, 19
	mov DWORD PTR [edi+4], eax
	movzx eax, BYTE PTR [esi+3]
	ror eax, 28
	add ebx, eax
	mov eax, ebx
	and eax, 1023
	shr ebx, 10
	ror eax, 19
	mov DWORD PTR [edi+8], eax
	movzx eax, BYTE PTR [esi+4]
	ror eax, 30
	add ebx, eax
	mov eax, ebx
	and eax, 1023
	shr ebx, 10
	ror eax, 19
	mov DWORD PTR [edi+12], eax
	add esi, 5
	add edi, 16
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
