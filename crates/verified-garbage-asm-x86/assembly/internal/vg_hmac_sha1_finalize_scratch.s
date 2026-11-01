// The functions of `src/internal/vg_hmac_sha1_finalize_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_finalize_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+160], ebx
	mov DWORD PTR [eax+164], esi
	mov DWORD PTR [eax+168], edi
	mov DWORD PTR [eax+172], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 176
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [ebp+176]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [ebp+180]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [ebp+184]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [ebp+188]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [ebp+192]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+52], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov ecx, -1610481664
	mov DWORD PTR [ebx+80], ecx
	mov eax, ebx
	add eax, 20
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha1_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+160]
	mov esi, DWORD PTR [eax+164]
	mov edi, DWORD PTR [eax+168]
	mov ebp, DWORD PTR [eax+172]
	ret
	.p2align 6
