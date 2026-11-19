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
	cmp eax, 256
	jb 29f
	mov ecx, eax
	shr ecx, 5
	lea esp, [esp-512]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [esp+16], eax
	mov eax, 0
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [esp+20], ecx
	mov eax, DWORD PTR [edi]
	add eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+4]
	adc eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+8]
	adc eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+12]
	adc eax, DWORD PTR [edi+84]
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
	lea esp, [esp-12]
	stmxcsr DWORD PTR [esp+4]
	mov eax, 8127
	mov DWORD PTR [esp], eax
	ldmxcsr DWORD PTR [esp]
	lfence
	mov eax, 67108863
	movd xmm5, eax
	punpcklqdq xmm5, xmm5
	movdqu XMMWORD PTR [esp+396], xmm5
	mov eax, 16777216
	movd xmm6, eax
	punpcklqdq xmm6, xmm6
	movdqu XMMWORD PTR [esp+412], xmm6
	movq xmm6, QWORD PTR [edi]
	psrlq xmm6, 0
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [edi+72]
	psrlq xmm6, 0
	pand xmm6, xmm5
	movdqa xmm1, xmm0
	punpcklqdq xmm1, xmm1
	movdqu XMMWORD PTR [esp+76], xmm1
	punpcklqdq xmm0, xmm6
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqa xmm7, xmm1
	psllq xmm7, 2
	paddq xmm7, xmm1
	movdqu XMMWORD PTR [esp+156], xmm7
	movdqa xmm7, xmm0
	psllq xmm7, 2
	paddq xmm7, xmm0
	movdqu XMMWORD PTR [esp+316], xmm7
	movq xmm6, QWORD PTR [edi]
	psrlq xmm6, 26
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [edi+72]
	psrlq xmm6, 26
	pand xmm6, xmm5
	movdqa xmm1, xmm0
	punpcklqdq xmm1, xmm1
	movdqu XMMWORD PTR [esp+92], xmm1
	punpcklqdq xmm0, xmm6
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqa xmm7, xmm1
	psllq xmm7, 2
	paddq xmm7, xmm1
	movdqu XMMWORD PTR [esp+172], xmm7
	movdqa xmm7, xmm0
	psllq xmm7, 2
	paddq xmm7, xmm0
	movdqu XMMWORD PTR [esp+332], xmm7
	movq xmm6, QWORD PTR [edi+6]
	psrlq xmm6, 4
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [edi+78]
	psrlq xmm6, 4
	pand xmm6, xmm5
	movdqa xmm1, xmm0
	punpcklqdq xmm1, xmm1
	movdqu XMMWORD PTR [esp+108], xmm1
	punpcklqdq xmm0, xmm6
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqa xmm7, xmm1
	psllq xmm7, 2
	paddq xmm7, xmm1
	movdqu XMMWORD PTR [esp+188], xmm7
	movdqa xmm7, xmm0
	psllq xmm7, 2
	paddq xmm7, xmm0
	movdqu XMMWORD PTR [esp+348], xmm7
	movq xmm6, QWORD PTR [edi+8]
	psrlq xmm6, 14
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [edi+80]
	psrlq xmm6, 14
	pand xmm6, xmm5
	movdqa xmm1, xmm0
	punpcklqdq xmm1, xmm1
	movdqu XMMWORD PTR [esp+124], xmm1
	punpcklqdq xmm0, xmm6
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqa xmm7, xmm1
	psllq xmm7, 2
	paddq xmm7, xmm1
	movdqu XMMWORD PTR [esp+204], xmm7
	movdqa xmm7, xmm0
	psllq xmm7, 2
	paddq xmm7, xmm0
	movdqu XMMWORD PTR [esp+364], xmm7
	movq xmm6, QWORD PTR [edi+13]
	psrlq xmm6, 0
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [edi+80]
	psrlq xmm6, 40
	pand xmm6, xmm5
	movdqa xmm1, xmm0
	punpcklqdq xmm1, xmm1
	movdqu XMMWORD PTR [esp+140], xmm1
	punpcklqdq xmm0, xmm6
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqa xmm7, xmm1
	psllq xmm7, 2
	paddq xmm7, xmm1
	movdqu XMMWORD PTR [esp+220], xmm7
	movdqa xmm7, xmm0
	psllq xmm7, 2
	paddq xmm7, xmm0
	movdqu XMMWORD PTR [esp+380], xmm7
	movq xmm6, QWORD PTR [esp+12]
	psrlq xmm6, 0
	pand xmm6, xmm5
	movdqa xmm0, xmm6
	movq xmm6, QWORD PTR [esp+12]
	psrlq xmm6, 26
	pand xmm6, xmm5
	movdqa xmm1, xmm6
	movq xmm6, QWORD PTR [esp+18]
	psrlq xmm6, 4
	pand xmm6, xmm5
	movdqa xmm2, xmm6
	movq xmm6, QWORD PTR [esp+20]
	psrlq xmm6, 14
	pand xmm6, xmm5
	movdqa xmm3, xmm6
	movq xmm6, QWORD PTR [esp+20]
	psrlq xmm6, 40
	pand xmm6, xmm5
	movdqa xmm4, xmm6
	mov eax, DWORD PTR [esp+28]
	and eax, 7
	movd xmm6, eax
	psllq xmm6, 24
	paddq xmm4, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+16]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 0
	pand xmm6, xmm5
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+16]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 26
	pand xmm6, xmm5
	paddq xmm1, xmm6
	movq xmm6, QWORD PTR [esi+6]
	movq xmm7, QWORD PTR [esi+22]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 4
	pand xmm6, xmm5
	paddq xmm2, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+24]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 14
	pand xmm6, xmm5
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+24]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 40
	pand xmm6, xmm5
	paddq xmm4, xmm6
	movdqu xmm7, XMMWORD PTR [esp+412]
	paddq xmm4, xmm7
	add esi, 32
	mov ecx, DWORD PTR [esp+32]
	sub ecx, 1
211:
	movdqu xmm5, XMMWORD PTR [esp+92]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+76]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+220]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+204]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+188]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+428], xmm5
	movdqu xmm5, XMMWORD PTR [esp+108]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+92]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+76]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+220]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+204]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+444], xmm5
	movdqu xmm5, XMMWORD PTR [esp+124]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+108]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+92]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+76]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+220]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+460], xmm5
	movdqu xmm5, XMMWORD PTR [esp+76]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+220]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+204]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+188]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+172]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqa xmm7, xmm5
	movdqu xmm5, XMMWORD PTR [esp+140]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+124]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+108]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+92]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+76]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqa xmm4, xmm5
	movdqa xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [esp+428]
	movdqu xmm2, XMMWORD PTR [esp+444]
	movdqu xmm3, XMMWORD PTR [esp+460]
	movdqu xmm5, XMMWORD PTR [esp+396]
	movdqa xmm6, xmm0
	psrlq xmm6, 26
	pand xmm0, xmm5
	paddq xmm1, xmm6
	movdqa xmm6, xmm3
	psrlq xmm6, 26
	pand xmm3, xmm5
	paddq xmm4, xmm6
	movdqa xmm6, xmm1
	psrlq xmm6, 26
	pand xmm1, xmm5
	paddq xmm2, xmm6
	movdqa xmm6, xmm4
	psrlq xmm6, 26
	pand xmm4, xmm5
	movdqa xmm7, xmm6
	psllq xmm7, 2
	paddq xmm6, xmm7
	paddq xmm0, xmm6
	movdqa xmm6, xmm2
	psrlq xmm6, 26
	pand xmm2, xmm5
	paddq xmm3, xmm6
	movdqa xmm6, xmm0
	psrlq xmm6, 26
	pand xmm0, xmm5
	paddq xmm1, xmm6
	movdqa xmm6, xmm3
	psrlq xmm6, 26
	pand xmm3, xmm5
	paddq xmm4, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+16]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 0
	pand xmm6, xmm5
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+16]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 26
	pand xmm6, xmm5
	paddq xmm1, xmm6
	movq xmm6, QWORD PTR [esi+6]
	movq xmm7, QWORD PTR [esi+22]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 4
	pand xmm6, xmm5
	paddq xmm2, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+24]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 14
	pand xmm6, xmm5
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+24]
	punpcklqdq xmm6, xmm7
	psrlq xmm6, 40
	pand xmm6, xmm5
	paddq xmm4, xmm6
	movdqu xmm7, XMMWORD PTR [esp+412]
	paddq xmm4, xmm7
	add esi, 32
	sub ecx, 1
	jne 211b
	movdqu xmm5, XMMWORD PTR [esp+252]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+236]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+380]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+364]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+348]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+428], xmm5
	movdqu xmm5, XMMWORD PTR [esp+268]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+252]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+236]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+380]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+364]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+444], xmm5
	movdqu xmm5, XMMWORD PTR [esp+284]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+268]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+252]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+236]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+380]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqu XMMWORD PTR [esp+460], xmm5
	movdqu xmm5, XMMWORD PTR [esp+236]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+380]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+364]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+348]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+332]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqa xmm7, xmm5
	movdqu xmm5, XMMWORD PTR [esp+300]
	pmuludq xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esp+284]
	pmuludq xmm6, xmm1
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+268]
	pmuludq xmm6, xmm2
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+252]
	pmuludq xmm6, xmm3
	paddq xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [esp+236]
	pmuludq xmm6, xmm4
	paddq xmm5, xmm6
	movdqa xmm4, xmm5
	movdqa xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [esp+428]
	movdqu xmm2, XMMWORD PTR [esp+444]
	movdqu xmm3, XMMWORD PTR [esp+460]
	movdqu xmm5, XMMWORD PTR [esp+396]
	movdqa xmm6, xmm0
	psrldq xmm6, 8
	paddq xmm0, xmm6
	movdqa xmm6, xmm1
	psrldq xmm6, 8
	paddq xmm1, xmm6
	movdqa xmm6, xmm2
	psrldq xmm6, 8
	paddq xmm2, xmm6
	movdqa xmm6, xmm3
	psrldq xmm6, 8
	paddq xmm3, xmm6
	movdqa xmm6, xmm4
	psrldq xmm6, 8
	paddq xmm4, xmm6
	movdqa xmm6, xmm0
	psrlq xmm6, 26
	pand xmm0, xmm5
	paddq xmm1, xmm6
	movdqa xmm6, xmm3
	psrlq xmm6, 26
	pand xmm3, xmm5
	paddq xmm4, xmm6
	movdqa xmm6, xmm1
	psrlq xmm6, 26
	pand xmm1, xmm5
	paddq xmm2, xmm6
	movdqa xmm6, xmm4
	psrlq xmm6, 26
	pand xmm4, xmm5
	movdqa xmm7, xmm6
	psllq xmm7, 2
	paddq xmm6, xmm7
	paddq xmm0, xmm6
	movdqa xmm6, xmm2
	psrlq xmm6, 26
	pand xmm2, xmm5
	paddq xmm3, xmm6
	movdqa xmm6, xmm0
	psrlq xmm6, 26
	pand xmm0, xmm5
	paddq xmm1, xmm6
	movdqa xmm6, xmm3
	psrlq xmm6, 26
	pand xmm3, xmm5
	paddq xmm4, xmm6
	movq QWORD PTR [esp+476], xmm0
	movq QWORD PTR [esp+484], xmm1
	movq QWORD PTR [esp+492], xmm2
	movq QWORD PTR [esp+500], xmm3
	movq QWORD PTR [esp+508], xmm4
	lfence
	ldmxcsr DWORD PTR [esp+4]
	lea esp, [esp+12]
	mov ebx, DWORD PTR [esp+464]
	mov eax, DWORD PTR [esp+472]
	mov ecx, 67108864
	mul ecx
	add ebx, eax
	mov DWORD PTR [edi], ebx
	adc edx, 0
	mov ebx, edx
	mov eax, DWORD PTR [esp+480]
	mov ecx, 1048576
	mul ecx
	add ebx, eax
	mov DWORD PTR [edi+4], ebx
	adc edx, 0
	mov ebx, edx
	mov eax, DWORD PTR [esp+488]
	mov ecx, 16384
	mul ecx
	add ebx, eax
	mov DWORD PTR [edi+8], ebx
	adc edx, 0
	mov ebx, edx
	mov eax, DWORD PTR [esp+496]
	mov ecx, 256
	mul ecx
	add ebx, eax
	mov DWORD PTR [edi+12], ebx
	adc edx, 0
	mov ebx, edx
	mov DWORD PTR [edi+16], ebx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	lea esp, [esp+512]
	jmp 210f
29:
210:
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	add eax, ecx
	sub eax, esi
	cmp eax, 16
	jb 212f
214:
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
	jae 214b
	jmp 213f
212:
213:
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	add eax, ecx
	sub eax, esi
	test eax, eax
	je 215f
	mov edx, edi
217:
	movzx ecx, BYTE PTR [esi]
	mov BYTE PTR [edx+56], cl
	add esi, 1
	add edx, 1
	sub eax, 1
	jne 217b
	jmp 216f
215:
216:
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
