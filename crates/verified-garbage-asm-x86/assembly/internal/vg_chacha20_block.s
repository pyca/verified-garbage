// The functions of `src/internal/vg_chacha20_block.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+4]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+68], esi
	mov DWORD PTR [eax+72], edi
	mov esi, eax
	mov edi, ecx
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi+60]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+20], ebx
	mov DWORD PTR [esi+40], ecx
	mov DWORD PTR [esi+60], edx
	mov eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+48]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+24], ebx
	mov DWORD PTR [esi+44], ecx
	mov DWORD PTR [esi+48], edx
	mov eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+52]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+28], ebx
	mov DWORD PTR [esi+32], ecx
	mov DWORD PTR [esi+52], edx
	mov eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+56]
	add eax, ebx
	xor edx, eax
	ror edx, 16
	add ecx, edx
	xor ebx, ecx
	ror ebx, 20
	add eax, ebx
	xor edx, eax
	ror edx, 24
	add ecx, edx
	xor ebx, ecx
	ror ebx, 25
	mov DWORD PTR [esi+12], eax
	mov DWORD PTR [esi+16], ebx
	mov DWORD PTR [esi+36], ecx
	mov DWORD PTR [esi+56], edx
	mov eax, DWORD PTR [esi]
	add eax, DWORD PTR [edi]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [edi+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	add eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	add eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	add eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	add eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	add eax, DWORD PTR [edi+32]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	add eax, DWORD PTR [edi+36]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	add eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	add eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	add eax, DWORD PTR [edi+48]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	add eax, DWORD PTR [edi+52]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	add eax, DWORD PTR [edi+56]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	add eax, DWORD PTR [edi+60]
	mov DWORD PTR [esi+60], eax
	mov eax, esi
	mov ebx, DWORD PTR [eax+64]
	mov esi, DWORD PTR [eax+68]
	mov edi, DWORD PTR [eax+72]
	ret
	.p2align 6
