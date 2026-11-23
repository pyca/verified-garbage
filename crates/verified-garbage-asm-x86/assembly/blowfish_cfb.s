// The functions of `src/blowfish_cfb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_cfb64_encrypt_ssse3:
	lea esp, [esp-452]
	mov eax, DWORD PTR [esp+456]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+460]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+464]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+468]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+404], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+12], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, DWORD PTR [edi+8]
	bswap edx
	mov ebp, DWORD PTR [edi+12]
	bswap ebp
	call {vg_blowfish_encrypt_block_ssse3}
	bswap ecx
	bswap edx
	mov DWORD PTR [edi+8], ecx
	mov DWORD PTR [edi+12], edx
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+400], esi
	mov DWORD PTR [edi+404], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+384]
	mov esi, DWORD PTR [edi+388]
	mov ebp, DWORD PTR [edi+396]
	mov edi, DWORD PTR [edi+392]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	lea esp, [esp+452]
	lea esp, [esp-460]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+456], ecx
	lea esp, [esp+460]
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

vg_blowfish_cfb64_encrypt:
	lea esp, [esp-112]
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+48], ebx
	mov DWORD PTR [eax+52], esi
	mov DWORD PTR [eax+56], edi
	mov DWORD PTR [eax+60], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+68], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+44], eax
	mov ebp, edi
	mov ebx, ebp
	add ebx, 40
	mov DWORD PTR [ebp+32], ebx
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebp+44], eax
	mov edi, ebp
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+48]
	mov esi, DWORD PTR [edi+52]
	mov ebp, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+56]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	lea esp, [esp+112]
	lea esp, [esp-112]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+112]
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

vg_blowfish_cfb64_decrypt_ssse3:
	lea esp, [esp-916]
	mov eax, DWORD PTR [esp+920]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+924]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+928]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+932]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+848], ebx
	mov DWORD PTR [eax+852], esi
	mov DWORD PTR [eax+856], edi
	mov DWORD PTR [eax+860], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+868], eax
	test eax, eax
	mov eax, DWORD PTR [edi+868]
	cmp eax, 16
	jb 20f
22:
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+508], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+876], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, esi
	add edx, 4096
	call {vg_blowfish_crypt_blocks16_ssse3}
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+400]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+404]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+448]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+452]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+456]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+460]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+464]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+468]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+472]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+476]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+480]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+484]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+488]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+492]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+496]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+500]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+504]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+508]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 16
	mov DWORD PTR [edi+864], esi
	mov DWORD PTR [edi+868], ebp
	cmp ebp, 16
	jae 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [edi+868]
	cmp eax, 8
	jb 23f
25:
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+876], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, esi
	add edx, 4096
	call {vg_blowfish_crypt_blocks16_ssse3}
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+400]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+404]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+416]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+420]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+424]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+428]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+432]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+436]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+440]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+444]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 8
	mov DWORD PTR [edi+864], esi
	mov DWORD PTR [edi+868], ebp
	cmp ebp, 8
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+868]
	cmp eax, 4
	jb 26f
28:
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+876], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, esi
	add edx, 4096
	call {vg_blowfish_crypt_blocks16_ssse3}
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+400]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+404]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 4
	mov DWORD PTR [edi+864], esi
	mov DWORD PTR [edi+868], ebp
	cmp ebp, 4
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+868]
	cmp eax, 2
	jb 29f
211:
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+876], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, esi
	add edx, 4096
	call {vg_blowfish_crypt_blocks16_ssse3}
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+392]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+396]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 2
	mov DWORD PTR [edi+864], esi
	mov DWORD PTR [edi+868], ebp
	cmp ebp, 2
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [edi+868]
	test eax, eax
	je 212f
214:
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+876], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, esi
	add edx, 4096
	call {vg_blowfish_crypt_blocks16_ssse3}
	mov esi, DWORD PTR [edi+864]
	mov ebp, DWORD PTR [edi+868]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+384]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+388]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+864], esi
	mov DWORD PTR [edi+868], ebp
	jne 214b
	jmp 213f
212:
213:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+848]
	mov esi, DWORD PTR [edi+852]
	mov ebp, DWORD PTR [edi+860]
	mov edi, DWORD PTR [edi+856]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	lea esp, [esp+916]
	lea esp, [esp-924]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+920], ecx
	lea esp, [esp+924]
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

vg_blowfish_cfb64_decrypt:
	lea esp, [esp-112]
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+48], ebx
	mov DWORD PTR [eax+52], esi
	mov DWORD PTR [eax+56], edi
	mov DWORD PTR [eax+60], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+68], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+44], eax
	mov ebp, edi
	mov ebx, ebp
	add ebx, 40
	mov DWORD PTR [ebp+32], ebx
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebp+44], eax
	mov edi, ebp
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+48]
	mov esi, DWORD PTR [edi+52]
	mov ebp, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+56]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	lea esp, [esp+112]
	lea esp, [esp-112]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+112]
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

vg_blowfish_cfb64_encrypt_final_ssse3:
	lea esp, [esp-452]
	mov eax, DWORD PTR [esp+456]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+460]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+464]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+468]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+404], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+12], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, DWORD PTR [edi+8]
	bswap edx
	mov ebp, DWORD PTR [edi+12]
	bswap ebp
	call {vg_blowfish_encrypt_block_ssse3}
	bswap ecx
	bswap edx
	mov DWORD PTR [edi+8], ecx
	mov DWORD PTR [edi+12], edx
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	cmp ebp, 8
	jb 23f
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+400], esi
	mov DWORD PTR [edi+404], ebp
	jmp 24f
23:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+412], eax
	mov ebx, edi
	add ebx, 8
25:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 25b
	mov DWORD PTR [edi+400], esi
	mov DWORD PTR [edi+404], ebp
24:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+384]
	mov esi, DWORD PTR [edi+388]
	mov ebp, DWORD PTR [edi+396]
	mov edi, DWORD PTR [edi+392]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	lea esp, [esp+452]
	lea esp, [esp-460]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+456], ecx
	lea esp, [esp+460]
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

vg_blowfish_cfb64_encrypt_final:
	lea esp, [esp-112]
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+48], ebx
	mov DWORD PTR [eax+52], esi
	mov DWORD PTR [eax+56], edi
	mov DWORD PTR [eax+60], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+68], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+44], eax
	mov ebp, edi
	mov ebx, ebp
	add ebx, 40
	mov DWORD PTR [ebp+32], ebx
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebp+44], eax
	mov edi, ebp
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	cmp ebp, 8
	jb 28f
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
	jmp 29f
28:
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+76], eax
	mov ebx, edi
	add ebx, 40
210:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 210b
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
29:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+48]
	mov esi, DWORD PTR [edi+52]
	mov ebp, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+56]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	lea esp, [esp+112]
	lea esp, [esp-112]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+112]
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

vg_blowfish_cfb64_decrypt_final_ssse3:
	lea esp, [esp-452]
	mov eax, DWORD PTR [esp+456]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+460]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+464]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+468]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+404], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+12], eax
	mov esi, DWORD PTR [esp+4]
	mov edx, DWORD PTR [edi+8]
	bswap edx
	mov ebp, DWORD PTR [edi+12]
	bswap ebp
	call {vg_blowfish_encrypt_block_ssse3}
	bswap ecx
	bswap edx
	mov DWORD PTR [edi+8], ecx
	mov DWORD PTR [edi+12], edx
	mov esi, DWORD PTR [edi+400]
	mov ebp, DWORD PTR [edi+404]
	cmp ebp, 8
	jb 23f
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+400], esi
	mov DWORD PTR [edi+404], ebp
	jmp 24f
23:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+412], eax
	mov ebx, edi
	add ebx, 8
25:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 25b
	mov DWORD PTR [edi+400], esi
	mov DWORD PTR [edi+404], ebp
24:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+384]
	mov esi, DWORD PTR [edi+388]
	mov ebp, DWORD PTR [edi+396]
	mov edi, DWORD PTR [edi+392]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	lea esp, [esp+452]
	lea esp, [esp-460]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+456], ecx
	lea esp, [esp+460]
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

vg_blowfish_cfb64_decrypt_final:
	lea esp, [esp-112]
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+48], ebx
	mov DWORD PTR [eax+52], esi
	mov DWORD PTR [eax+56], edi
	mov DWORD PTR [eax+60], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+68], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+44], eax
	mov ebp, edi
	mov ebx, ebp
	add ebx, 40
	mov DWORD PTR [ebp+32], ebx
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebp+44], eax
	mov edi, ebp
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	cmp ebp, 8
	jb 28f
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
	jmp 29f
28:
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+76], eax
	mov ebx, edi
	add ebx, 40
210:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 210b
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
29:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+48]
	mov esi, DWORD PTR [edi+52]
	mov ebp, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+56]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	lea esp, [esp+112]
	lea esp, [esp-112]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+112]
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
