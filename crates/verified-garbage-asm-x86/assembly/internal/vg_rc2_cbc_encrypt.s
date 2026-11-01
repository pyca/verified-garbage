// The functions of `src/internal/vg_rc2_cbc_encrypt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+264], ebp
	mov DWORD PTR [eax+268], ebx
	mov DWORD PTR [eax+272], esi
	mov DWORD PTR [eax+276], edi
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+16]
	cmp edi, 0
	je 20f
22:
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ecx]
	xor edx, DWORD PTR [ecx+4]
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], edx
	push ebp
	push esi
	push ebx
	call {vg_rc2_encrypt_block}
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+4]
	mov DWORD PTR [ecx], eax
	mov DWORD PTR [ecx+4], edx
	add esi, 8
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebp, DWORD PTR [eax+264]
	mov ebx, DWORD PTR [eax+268]
	mov esi, DWORD PTR [eax+272]
	mov edi, DWORD PTR [eax+276]
	ret
	.p2align 6
