// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	push ebx
	push esi
	push edi
	push ebp
	mov edi, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+36]
	mov eax, 0
20:
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 20b
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+32]
	mov ecx, edi
	add ecx, DWORD PTR [esp+28]
	mov ebp, DWORD PTR [esp+36]
	sub ebp, DWORD PTR [esp+28]
21:
	mov ebx, 0
22:
	mov edx, DWORD PTR [esi]
	cmp edx, 0
	jne 23f
	jmp 24f
23:
	mov edx, edi
	add edx, eax
	mov BYTE PTR [edx], bl
	add eax, 1
24:
	add esi, 4
	add ebx, 1
	cmp ebx, 256
	jne 22b
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub ebp, 1
	jne 21b
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
