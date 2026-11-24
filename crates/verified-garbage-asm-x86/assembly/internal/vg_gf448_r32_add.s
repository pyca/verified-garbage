// The functions of `src/internal/vg_gf448_r32_add.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r32_add:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	add esi, edi
	mov ebx, DWORD PTR [esp+16]
	add ebx, edi
	mov ebp, DWORD PTR [esp+8]
	add ebp, edi
	xor ecx, ecx
	mov eax, DWORD PTR [esi]
	adc eax, DWORD PTR [ebx]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [esi+4]
	adc eax, DWORD PTR [ebx+4]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [esi+8]
	adc eax, DWORD PTR [ebx+8]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [esi+12]
	adc eax, DWORD PTR [ebx+12]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [esi+16]
	adc eax, DWORD PTR [ebx+16]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [esi+20]
	adc eax, DWORD PTR [ebx+20]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [esi+24]
	adc eax, DWORD PTR [ebx+24]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [esi+28]
	adc eax, DWORD PTR [ebx+28]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi+32]
	adc eax, DWORD PTR [ebx+32]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [esi+36]
	adc eax, DWORD PTR [ebx+36]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [esi+40]
	adc eax, DWORD PTR [ebx+40]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [esi+44]
	adc eax, DWORD PTR [ebx+44]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [esi+48]
	adc eax, DWORD PTR [ebx+48]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [esi+52]
	adc eax, DWORD PTR [ebx+52]
	mov DWORD PTR [ebp+52], eax
	sbb ecx, ecx
	and ecx, 1
	mov eax, DWORD PTR [ebp]
	adc eax, ecx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, 0
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, 0
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, 0
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, 0
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, 0
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, ecx
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	adc eax, 0
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	adc eax, 0
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	adc eax, 0
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	adc eax, 0
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+48]
	adc eax, 0
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	adc eax, 0
	mov DWORD PTR [ebp+52], eax
	sbb ecx, ecx
	and ecx, 1
	mov eax, DWORD PTR [ebp]
	adc eax, ecx
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	adc eax, 0
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	adc eax, 0
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	adc eax, 0
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+16]
	adc eax, 0
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	adc eax, 0
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	adc eax, 0
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	adc eax, ecx
	mov DWORD PTR [ebp+28], eax
	mov ebx, DWORD PTR [edi+4080]
	mov esi, DWORD PTR [edi+4084]
	mov ebp, DWORD PTR [edi+4092]
	mov edi, DWORD PTR [edi+4088]
	ret
	.p2align 6
