// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [esp+24]
	mov ebp, -1
	mov ecx, 256
20:
	mov eax, DWORD PTR [esi]
	mov edx, 8380417
	sub edx, eax
	cmp eax, ebx
	sbb eax, eax
	cmp edx, ebx
	sbb edx, edx
	or eax, edx
	and ebp, eax
	add esi, 4
	sub ecx, 1
	jne 20b
	mov eax, ebp
	and eax, 1
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
