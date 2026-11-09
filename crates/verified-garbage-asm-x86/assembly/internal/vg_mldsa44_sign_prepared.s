// The functions of `src/internal/vg_mldsa44_sign_prepared.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_prepared:
	push ebx
	push esi
	push edi
	push ebp
	mov esi, DWORD PTR [esp+36]
	mov eax, 1
	mov DWORD PTR [esi+1104], eax
	mov edi, DWORD PTR [esp+20]
	add edi, 2560
	mov ebp, esi
	add ebp, 26624
	mov ecx, 3072
20:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [ebp], eax
	add edi, 4
	add ebp, 4
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+20]
	add eax, 0
	mov ecx, DWORD PTR [esp+24]
	add ecx, 0
	mov edx, DWORD PTR [esp+28]
	add edx, 0
	mov ebx, DWORD PTR [esp+32]
	add ebx, 0
	mov edi, esi
	add edi, 0
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_mldsa44_sign_core}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
