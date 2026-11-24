// The functions of `src/internal/vg_gf448_r32_mul_a24.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf448_r32_mul_a24:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+4080], ebx
	mov DWORD PTR [eax+4084], esi
	mov DWORD PTR [eax+4088], edi
	mov DWORD PTR [eax+4092], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	add esi, edi
	mov ebp, DWORD PTR [esp+8]
	add ebp, edi
	mov ebx, 39081
	mov ecx, 0
	mov eax, DWORD PTR [esi]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+4]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+4], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+8]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+8], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+12]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+12], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+16]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+16], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+20]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+20], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+24]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+24], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+28]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+28], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+32]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+32], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+36]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+36], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+40]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+40], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+44]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+44], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+48]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+48], eax
	mov ecx, edx
	mov eax, DWORD PTR [esi+52]
	mul ebx
	add eax, ecx
	adc edx, 0
	mov DWORD PTR [ebp+52], eax
	mov ecx, edx
	test ecx, ecx
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
