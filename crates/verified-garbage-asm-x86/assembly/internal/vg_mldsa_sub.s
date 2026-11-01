// The functions of `src/internal/vg_mldsa_sub.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sub:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	mov ecx, 256
20:
	mov eax, DWORD PTR [esi]
	add eax, 8380417
	sub eax, DWORD PTR [edi]
	sub eax, 8380417
	sbb edx, edx
	and edx, 8380417
	add eax, edx
	mov DWORD PTR [esi], eax
	add esi, 4
	add edi, 4
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
