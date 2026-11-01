// The functions of `src/internal/vg_keccak_squeeze_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_squeeze_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	add ecx, ebx
	mov DWORD PTR [ebp+528], ecx
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+532], ecx
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, ecx
	sub eax, ebx
	cmp eax, edx
	je 23f
	jmp 24f
23:
	mov DWORD PTR [ebp+528], ebx
	push ebp
	push ebx
	call {vg_keccak_f1600}
	pop eax
	pop eax
24:
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	movzx eax, BYTE PTR [ecx]
	mov BYTE PTR [esi], al
	add ecx, 1
	mov DWORD PTR [ebp+528], ecx
	mov DWORD PTR [ebp+532], edx
	add esi, 1
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+528]
	sub eax, ebx
	mov ecx, ebp
	mov ebx, DWORD PTR [ecx+512]
	mov esi, DWORD PTR [ecx+516]
	mov edi, DWORD PTR [ecx+520]
	mov ebp, DWORD PTR [ecx+524]
	ret
	.p2align 6
