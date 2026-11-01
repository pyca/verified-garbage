// The functions of `src/internal/vg_hmac_md5_finalize_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_finalize_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 128
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_md5_finalize_scratch}
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
	mov ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+32], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 0
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
	mov ecx, 640
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	ret
	.p2align 6
