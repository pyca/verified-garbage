// The functions of `src/internal/vg_mldsa_multiply_add_ntt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_add_ntt:
	push ebx
	push esi
	push edi
	push ebp
	mov ebp, DWORD PTR [esp+20]
	mov esi, DWORD PTR [esp+24]
	mov edi, DWORD PTR [esp+28]
	mov ecx, 256
20:
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [edi]
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	mov eax, ebx
	mov edx, 2365951
	mul edx
	mov ebx, edx
	mov edx, -58728449
	mul edx
	mov edx, 8380417
	mul edx
	add eax, -1
	adc ebx, edx
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	add ebx, DWORD PTR [ebp]
	sub ebx, 8380417
	sbb edx, edx
	and edx, 8380417
	add ebx, edx
	mov DWORD PTR [ebp], ebx
	add esi, 4
	add edi, 4
	add ebp, 4
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
