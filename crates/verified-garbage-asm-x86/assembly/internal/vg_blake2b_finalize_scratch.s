// The functions of `src/internal/vg_blake2b_finalize_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_finalize_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov edx, ebx
	add edx, eax
	mov ecx, 128
	sub ecx, eax
	mov eax, 0
	je 22f
24:
	mov BYTE PTR [edx+64], al
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+32]
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+36]
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+40]
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+44]
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+48]
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+52]
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+56]
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+60]
	mov DWORD PTR [eax+60], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	ret
	.p2align 6
