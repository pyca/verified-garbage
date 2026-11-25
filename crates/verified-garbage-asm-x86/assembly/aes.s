// The functions of `src/aes.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key:
	lea esp, [esp-532]
	mov eax, DWORD PTR [esp+536]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+540]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+544]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+256], ebx
	mov DWORD PTR [eax+260], esi
	mov DWORD PTR [eax+264], edi
	mov DWORD PTR [eax+268], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
20:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov esi, ebp
	sub esi, 4
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+280], eax
	shr eax, 2
	mov ebx, eax
	add eax, eax
	add eax, ebx
	add eax, 28
	mov DWORD PTR [edi+284], eax
	mov eax, 1
	mov DWORD PTR [edi+272], eax
21:
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [edi+276]
	test ecx, ecx
	je 22f
	cmp ecx, 16
	je 24f
	jmp 25f
24:
	mov ecx, DWORD PTR [edi+280]
	cmp ecx, 32
	je 26f
	jmp 27f
26:
	mov DWORD PTR [edi], eax
	shr eax, 1
	mov DWORD PTR [edi+4], eax
	shr eax, 1
	mov DWORD PTR [edi+8], eax
	shr eax, 1
	mov DWORD PTR [edi+12], eax
	shr eax, 1
	mov DWORD PTR [edi+16], eax
	shr eax, 1
	mov DWORD PTR [edi+20], eax
	shr eax, 1
	mov DWORD PTR [edi+24], eax
	shr eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+4]
	xor ebx, eax
	mov ecx, DWORD PTR [edi+24]
	xor ecx, ebx
	mov edx, DWORD PTR [edi]
	xor edx, ebx
	mov ebp, DWORD PTR [edi+12]
	xor ebp, ecx
	xor ebp, DWORD PTR [edi+28]
	mov DWORD PTR [edi], ebx
	mov ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ebp
	mov DWORD PTR [edi+12], eax
	mov eax, ebx
	xor eax, edx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [edi+16]
	xor ecx, eax
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+32]
	xor ecx, eax
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+16]
	xor edx, ebx
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+16], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, eax
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+4]
	xor eax, edx
	mov DWORD PTR [edi+4], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [edi+56], eax
	mov eax, ebp
	and eax, ecx
	mov DWORD PTR [edi+60], ecx
	mov ecx, DWORD PTR [edi+48]
	and ecx, edx
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+4]
	and edx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+44]
	xor eax, edx
	xor ecx, eax
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+12]
	and ebp, DWORD PTR [edi+44]
	xor ecx, ebp
	xor ebx, ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+76], ebx
	mov ebx, DWORD PTR [edi+28]
	and ebx, DWORD PTR [edi]
	xor ecx, edx
	mov edx, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+36]
	xor ebp, ecx
	xor ebx, edx
	xor ecx, ebx
	mov ebx, DWORD PTR [edi+56]
	and ebx, DWORD PTR [edi+72]
	xor ebx, eax
	xor edx, ebx
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+20]
	and ebx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi+8]
	xor ebp, ebx
	xor ecx, eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov ebx, ecx
	and ebx, edx
	xor eax, ebp
	mov ebp, DWORD PTR [edi+76]
	xor ebp, edx
	xor ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi+76]
	xor ecx, ebx
	xor ebx, eax
	and ebp, ebx
	xor ebp, DWORD PTR [edi+76]
	xor edx, ebp
	mov ebx, ecx
	xor ebx, ebp
	and ebx, DWORD PTR [edi+76]
	xor edx, ebx
	xor ebx, ecx
	and ecx, DWORD PTR [edi+8]
	xor ecx, eax
	and ebx, ecx
	mov eax, ebp
	xor eax, edx
	xor ebx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi+20]
	and ecx, eax
	and eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+52]
	and eax, edx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+60]
	and eax, ebx
	mov DWORD PTR [edi+52], ecx
	mov ecx, ebx
	xor ecx, edx
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+40]
	and eax, ecx
	and edx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+28]
	and eax, ebp
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+68]
	and eax, ebx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+36]
	and eax, ecx
	xor ebx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi]
	and eax, ebp
	xor edx, eax
	mov DWORD PTR [edi], edx
	mov edx, DWORD PTR [edi+64]
	and edx, ebx
	xor ebp, DWORD PTR [edi+8]
	and ebx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+12]
	and eax, ebp
	xor edx, DWORD PTR [edi+60]
	xor ecx, ebp
	xor eax, edx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	and eax, ecx
	and ecx, DWORD PTR [edi+4]
	xor edx, eax
	xor ecx, DWORD PTR [edi+40]
	and ebp, DWORD PTR [edi+44]
	xor ebp, ebx
	xor ebp, ecx
	xor ecx, DWORD PTR [edi+36]
	xor ebx, DWORD PTR [edi+28]
	xor ebx, ecx
	xor ebx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+4], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+8]
	xor ecx, ebx
	xor edx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+16]
	xor ecx, DWORD PTR [edi+60]
	xor ecx, DWORD PTR [edi]
	xor ebp, ecx
	xor ecx, DWORD PTR [edi+16]
	xor ebx, ebp
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi]
	xor ecx, eax
	xor ebx, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi+40]
	xor edx, DWORD PTR [edi+32]
	xor ecx, DWORD PTR [edi+32]
	xor ebx, DWORD PTR [edi+28]
	and ecx, 16843009
	and eax, 16843009
	ror ecx, 31
	xor ecx, eax
	mov eax, DWORD PTR [edi+8]
	and eax, 16843009
	ror ecx, 31
	xor ecx, eax
	and ebx, 16843009
	ror ecx, 31
	xor ecx, ebx
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	mov edx, DWORD PTR [edi+4]
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	mov edx, DWORD PTR [edi+16]
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	and ebp, 16843009
	ror ecx, 31
	xor ecx, ebp
	mov eax, ecx
	xor eax, 1667457891
27:
25:
	jmp 23f
22:
	mov DWORD PTR [edi], eax
	shr eax, 1
	mov DWORD PTR [edi+4], eax
	shr eax, 1
	mov DWORD PTR [edi+8], eax
	shr eax, 1
	mov DWORD PTR [edi+12], eax
	shr eax, 1
	mov DWORD PTR [edi+16], eax
	shr eax, 1
	mov DWORD PTR [edi+20], eax
	shr eax, 1
	mov DWORD PTR [edi+24], eax
	shr eax, 1
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+4]
	xor ebx, eax
	mov ecx, DWORD PTR [edi+24]
	xor ecx, ebx
	mov edx, DWORD PTR [edi]
	xor edx, ebx
	mov ebp, DWORD PTR [edi+12]
	xor ebp, ecx
	xor ebp, DWORD PTR [edi+28]
	mov DWORD PTR [edi], ebx
	mov ebx, ebp
	xor ebx, eax
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+16]
	xor eax, ebp
	mov DWORD PTR [edi+12], eax
	mov eax, ebx
	xor eax, edx
	mov DWORD PTR [edi+32], ecx
	mov ecx, DWORD PTR [edi+20]
	xor ecx, eax
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [edi+16]
	xor ecx, eax
	mov DWORD PTR [edi+36], ecx
	mov ecx, DWORD PTR [edi+32]
	xor ecx, eax
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+44], edx
	mov edx, DWORD PTR [edi+16]
	xor edx, ebx
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+16], ebp
	mov ebp, DWORD PTR [edi+20]
	xor ebp, edx
	mov DWORD PTR [edi+48], ebp
	mov ebp, DWORD PTR [edi+36]
	xor ebp, eax
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+4]
	xor eax, edx
	mov DWORD PTR [edi+4], edx
	mov edx, ecx
	xor edx, eax
	mov DWORD PTR [edi+56], eax
	mov eax, ebp
	and eax, ecx
	mov DWORD PTR [edi+60], ecx
	mov ecx, DWORD PTR [edi+48]
	and ecx, edx
	mov DWORD PTR [edi+64], edx
	mov edx, DWORD PTR [edi+4]
	and edx, DWORD PTR [edi+16]
	mov DWORD PTR [edi+68], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, DWORD PTR [edi+44]
	xor eax, edx
	xor ecx, eax
	mov DWORD PTR [edi+72], ebp
	mov ebp, DWORD PTR [edi+12]
	and ebp, DWORD PTR [edi+44]
	xor ecx, ebp
	xor ebx, ecx
	mov ecx, DWORD PTR [edi+52]
	and ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+76], ebx
	mov ebx, DWORD PTR [edi+28]
	and ebx, DWORD PTR [edi]
	xor ecx, edx
	mov edx, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi+36]
	xor ebp, ecx
	xor ebx, edx
	xor ecx, ebx
	mov ebx, DWORD PTR [edi+56]
	and ebx, DWORD PTR [edi+72]
	xor ebx, eax
	xor edx, ebx
	mov eax, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+52]
	mov ebx, DWORD PTR [edi+20]
	and ebx, DWORD PTR [edi+24]
	xor edx, DWORD PTR [edi+8]
	xor ebp, ebx
	xor ecx, eax
	mov eax, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi]
	mov ebx, ecx
	and ebx, edx
	xor eax, ebp
	mov ebp, DWORD PTR [edi+76]
	xor ebp, edx
	xor ecx, eax
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi+76]
	xor ecx, ebx
	xor ebx, eax
	and ebp, ebx
	xor ebp, DWORD PTR [edi+76]
	xor edx, ebp
	mov ebx, ecx
	xor ebx, ebp
	and ebx, DWORD PTR [edi+76]
	xor edx, ebx
	xor ebx, ecx
	and ecx, DWORD PTR [edi+8]
	xor ecx, eax
	and ebx, ecx
	mov eax, ebp
	xor eax, edx
	xor ebx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi+20]
	and ecx, eax
	and eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+52]
	and eax, edx
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+60]
	and eax, ebx
	mov DWORD PTR [edi+52], ecx
	mov ecx, ebx
	xor ecx, edx
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+40]
	and eax, ecx
	and edx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+28]
	and eax, ebp
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+68]
	and eax, ebx
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+36]
	and eax, ecx
	xor ebx, DWORD PTR [edi+8]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi]
	and eax, ebp
	xor edx, eax
	mov DWORD PTR [edi], edx
	mov edx, DWORD PTR [edi+64]
	and edx, ebx
	xor ebp, DWORD PTR [edi+8]
	and ebx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+12]
	and eax, ebp
	xor edx, DWORD PTR [edi+60]
	xor ecx, ebp
	xor eax, edx
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+16]
	and eax, ecx
	and ecx, DWORD PTR [edi+4]
	xor edx, eax
	xor ecx, DWORD PTR [edi+40]
	and ebp, DWORD PTR [edi+44]
	xor ebp, ebx
	xor ebp, ecx
	xor ecx, DWORD PTR [edi+36]
	xor ebx, DWORD PTR [edi+28]
	xor ebx, ecx
	xor ebx, DWORD PTR [edi+52]
	mov DWORD PTR [edi+4], ebx
	mov ebx, DWORD PTR [edi+72]
	and ebx, DWORD PTR [edi+8]
	xor ecx, ebx
	xor edx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [edi+56]
	and ecx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+16]
	xor ecx, DWORD PTR [edi+60]
	xor ecx, DWORD PTR [edi]
	xor ebp, ecx
	xor ecx, DWORD PTR [edi+16]
	xor ebx, ebp
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [edi]
	xor ecx, eax
	xor ebx, DWORD PTR [edi+24]
	xor eax, DWORD PTR [edi+4]
	xor edx, DWORD PTR [edi+20]
	xor eax, DWORD PTR [edi+12]
	xor ebx, DWORD PTR [edi+40]
	xor edx, DWORD PTR [edi+32]
	xor ecx, DWORD PTR [edi+32]
	xor ebx, DWORD PTR [edi+28]
	and ecx, 16843009
	and eax, 16843009
	ror ecx, 31
	xor ecx, eax
	mov eax, DWORD PTR [edi+8]
	and eax, 16843009
	ror ecx, 31
	xor ecx, eax
	and ebx, 16843009
	ror ecx, 31
	xor ecx, ebx
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	mov edx, DWORD PTR [edi+4]
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	mov edx, DWORD PTR [edi+16]
	and edx, 16843009
	ror ecx, 31
	xor ecx, edx
	and ebp, 16843009
	ror ecx, 31
	xor ecx, ebp
	mov eax, ecx
	xor eax, 1667457891
	ror eax, 8
	xor eax, DWORD PTR [edi+272]
	mov ebx, DWORD PTR [edi+272]
	mov ecx, ebx
	shr ecx, 7
	mov edx, 0
	sub edx, ecx
	and edx, 27
	add ebx, ebx
	xor ebx, edx
	and ebx, 255
	mov DWORD PTR [edi+272], ebx
23:
	mov ecx, DWORD PTR [edi+280]
	mov ebx, esi
	add ebx, 4
	sub ebx, ecx
	xor eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+284]
	mov ebp, DWORD PTR [edi+280]
	mov DWORD PTR [esi+4], eax
	add esi, 4
	add ecx, 4
	cmp ecx, ebp
	je 28f
	jmp 29f
28:
	mov ecx, 0
29:
	mov DWORD PTR [edi+276], ecx
	mov DWORD PTR [edi+280], ebp
	sub edx, 1
	mov DWORD PTR [edi+284], edx
	jne 21b
	mov ebx, DWORD PTR [edi+256]
	mov esi, DWORD PTR [edi+260]
	mov ebp, DWORD PTR [edi+268]
	mov edi, DWORD PTR [edi+264]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	lea esp, [esp+532]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_expand_key_aesni:
	lea esp, [esp-532]
	mov eax, DWORD PTR [esp+536]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+540]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+544]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	cmp ecx, 24
	je 20f
	cmp ecx, 32
	je 22f
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [edx], xmm1
	aeskeygenassist xmm3, xmm1, 1
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+16], xmm1
	aeskeygenassist xmm3, xmm1, 2
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+32], xmm1
	aeskeygenassist xmm3, xmm1, 4
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	aeskeygenassist xmm3, xmm1, 8
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+64], xmm1
	aeskeygenassist xmm3, xmm1, 16
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+80], xmm1
	aeskeygenassist xmm3, xmm1, 32
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	aeskeygenassist xmm3, xmm1, 64
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+112], xmm1
	aeskeygenassist xmm3, xmm1, 128
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+128], xmm1
	aeskeygenassist xmm3, xmm1, 27
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+144], xmm1
	aeskeygenassist xmm3, xmm1, 54
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+160], xmm1
	jmp 23f
22:
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+16]
	movdqu XMMWORD PTR [edx], xmm1
	movdqu XMMWORD PTR [edx+16], xmm2
	aeskeygenassist xmm3, xmm2, 1
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+32], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+48], xmm2
	aeskeygenassist xmm3, xmm2, 2
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+64], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+80], xmm2
	aeskeygenassist xmm3, xmm2, 4
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+112], xmm2
	aeskeygenassist xmm3, xmm2, 8
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+128], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+144], xmm2
	aeskeygenassist xmm3, xmm2, 16
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+160], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+176], xmm2
	aeskeygenassist xmm3, xmm2, 32
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+192], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+208], xmm2
	aeskeygenassist xmm3, xmm2, 64
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+224], xmm1
23:
	jmp 21f
20:
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [edx], xmm1
	movdqu XMMWORD PTR [edx+16], xmm2
	aeskeygenassist xmm3, xmm2, 1
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+24], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+40], xmm2
	aeskeygenassist xmm3, xmm2, 2
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+64], xmm2
	aeskeygenassist xmm3, xmm2, 4
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+72], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+88], xmm2
	aeskeygenassist xmm3, xmm2, 8
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+112], xmm2
	aeskeygenassist xmm3, xmm2, 16
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+120], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+136], xmm2
	aeskeygenassist xmm3, xmm2, 32
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+144], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+160], xmm2
	aeskeygenassist xmm3, xmm2, 64
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+168], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+184], xmm2
	aeskeygenassist xmm3, xmm2, 128
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+192], xmm1
21:
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	lea esp, [esp+532]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
