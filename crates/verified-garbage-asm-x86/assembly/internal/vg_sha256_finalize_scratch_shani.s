// The functions of `src/internal/vg_sha256_finalize_scratch_shani.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_finalize_scratch_shani:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+136], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 63
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+32], cl
	add edi, 1
	mov esi, 0
	cmp edi, 57
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 64
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 56
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+32], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+128]
	mov ecx, DWORD PTR [ebp+132]
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+88], ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
29:
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+136]
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
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, DWORD PTR [ebp+112]
	mov esi, DWORD PTR [ebp+116]
	mov edi, DWORD PTR [ebp+120]
	mov ebp, DWORD PTR [ebp+124]
	ret
	.p2align 6
