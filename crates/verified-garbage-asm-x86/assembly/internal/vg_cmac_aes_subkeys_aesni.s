// The functions of `src/internal/vg_cmac_aes_subkeys_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys_aesni:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx+16], eax
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], edx
	mov DWORD PTR [ebx+28], esi
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6
