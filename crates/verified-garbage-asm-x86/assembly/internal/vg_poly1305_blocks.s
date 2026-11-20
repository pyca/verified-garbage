// The functions of `src/internal/vg_poly1305_blocks.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_blocks:
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [eax+116], ebx
	mov DWORD PTR [eax+120], esi
	mov DWORD PTR [eax+124], edi
	mov DWORD PTR [eax+20], ebp
	mov edi, eax
	mov eax, DWORD PTR [edi+24]
	and eax, 268435455
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+28]
	and eax, 268435452
	mov DWORD PTR [edi+76], eax
	mov ecx, eax
	shr ecx, 2
	add eax, ecx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+32]
	and eax, 268435452
	mov DWORD PTR [edi+80], eax
	mov ecx, eax
	shr ecx, 2
	add eax, ecx
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+36]
	and eax, 268435452
	mov DWORD PTR [edi+84], eax
	mov ecx, eax
	shr ecx, 2
	add eax, ecx
	mov DWORD PTR [edi+96], eax
	mov esi, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	test ecx, ecx
	je 20f
22:
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [esi]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	adc eax, 1
	mov DWORD PTR [edi+16], eax
	mov ebx, 0
	mov ebp, 0
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+72]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+96]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+92]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+88]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov DWORD PTR [edi+100], ebx
	mov ebx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+76]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+72]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+96]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+92]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+88]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov DWORD PTR [edi+104], ebx
	mov ebx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+80]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+76]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+72]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+96]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+92]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov DWORD PTR [edi+108], ebx
	mov ebx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+84]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+80]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+76]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+72]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+96]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov DWORD PTR [edi+112], ebx
	mov ebx, ebp
	mov ebp, 0
	mov eax, DWORD PTR [edi+16]
	mov ecx, DWORD PTR [edi+72]
	mul ecx
	add ebx, eax
	adc ebp, edx
	mov eax, ebx
	shr eax, 2
	mov ecx, eax
	add eax, eax
	add eax, eax
	add eax, ecx
	and ebx, 3
	add eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+104]
	adc eax, 0
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+108]
	adc eax, 0
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+112]
	adc eax, 0
	mov DWORD PTR [edi+12], eax
	adc ebx, 0
	mov DWORD PTR [edi+16], ebx
	add esi, 16
	mov eax, DWORD PTR [esp+12]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [esp+8]
	add eax, ecx
	cmp eax, esi
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [edi]
	add eax, 5
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, 0
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, 0
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+16]
	adc eax, 0
	mov edx, eax
	shr eax, 2
	mov ebp, 0
	sub ebp, eax
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+100]
	xor ecx, eax
	and ecx, ebp
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+104]
	xor ecx, eax
	and ecx, ebp
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+108]
	xor ecx, eax
	and ecx, ebp
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov ecx, DWORD PTR [edi+112]
	xor ecx, eax
	and ecx, ebp
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	xor edx, eax
	and edx, ebp
	xor eax, edx
	and eax, 3
	mov DWORD PTR [edi+16], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax+116]
	mov esi, DWORD PTR [eax+120]
	mov edi, DWORD PTR [eax+124]
	mov ebp, DWORD PTR [eax+20]
	mov ecx, 0
	mov DWORD PTR [eax+20], ecx
	ret
	.p2align 6
