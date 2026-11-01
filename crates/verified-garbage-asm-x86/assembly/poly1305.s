// The functions of `src/poly1305.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [eax+24], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [eax+28], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [eax+32], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [eax+36], edx
	mov edx, DWORD PTR [ecx+16]
	mov DWORD PTR [eax+40], edx
	mov edx, DWORD PTR [ecx+20]
	mov DWORD PTR [eax+44], edx
	mov edx, DWORD PTR [ecx+24]
	mov DWORD PTR [eax+48], edx
	mov edx, DWORD PTR [ecx+28]
	mov DWORD PTR [eax+52], edx
	mov edx, 0
	mov DWORD PTR [eax], edx
	mov DWORD PTR [eax+4], edx
	mov DWORD PTR [eax+8], edx
	mov DWORD PTR [eax+12], edx
	mov DWORD PTR [eax+16], edx
	mov DWORD PTR [eax+20], edx
	ret
	.p2align 6

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

vg_poly1305_update:
	lea esp, [esp-156]
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
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
	mov esi, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+8]
	and edx, 15
	test edx, edx
	je 20f
	mov eax, 16
	sub eax, edx
	mov ecx, DWORD PTR [esp+20]
	cmp ecx, eax
	jb 22f
	jmp 23f
22:
	mov eax, ecx
23:
	add edx, edi
	test eax, eax
	je 24f
26:
	movzx ecx, BYTE PTR [esi]
	mov BYTE PTR [edx+56], cl
	add esi, 1
	add edx, 1
	sub eax, 1
	jne 26b
	jmp 25f
24:
25:
	sub edx, edi
	cmp edx, 16
	je 27f
	jmp 28f
27:
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, DWORD PTR [edi+68]
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
28:
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	add eax, ecx
	sub eax, esi
	cmp eax, 16
	jb 29f
211:
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
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	add eax, ecx
	sub eax, esi
	cmp eax, 16
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	add eax, ecx
	sub eax, esi
	test eax, eax
	je 212f
	mov edx, edi
214:
	movzx ecx, BYTE PTR [esi]
	mov BYTE PTR [edx+56], cl
	add esi, 1
	add edx, 1
	sub eax, 1
	jne 214b
	jmp 213f
212:
213:
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
	lea esp, [esp+156]
	ret
	.p2align 6

vg_poly1305_finalize:
	lea esp, [esp-152]
	mov eax, DWORD PTR [esp+156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
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
	mov edx, DWORD PTR [esp+8]
	and edx, 15
	test edx, edx
	je 20f
	mov eax, 0
	mov ecx, edx
	add ecx, edi
22:
	mov BYTE PTR [ecx+56], al
	add ecx, 1
	add edx, 1
	cmp edx, 16
	jne 22b
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	and ecx, 15
	add ecx, edi
	mov BYTE PTR [ecx+56], al
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	adc eax, 0
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
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, DWORD PTR [edi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, DWORD PTR [edi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, edi
	mov ebx, DWORD PTR [eax+116]
	mov esi, DWORD PTR [eax+120]
	mov edi, DWORD PTR [eax+124]
	mov ebp, DWORD PTR [eax+20]
	mov ecx, 0
	mov DWORD PTR [eax+20], ecx
	lea esp, [esp+152]
	ret
	.p2align 6
