// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal_aesni_pclmul:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 24f
	mov ecx, 64
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
26:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
212:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 28f
27:
28:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 213f
215:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
218:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 215b
	jmp 214f
213:
214:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 219f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
224:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 225f
	mov ecx, 64
	jmp 226f
225:
226:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
227:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 227b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 228f
	mov edx, DWORD PTR [ebp+96]
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edi, DWORD PTR [ebp+176]
	cmp edi, 96
	jb 230f
232:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	add edx, 1
	movd xmm1, edx
	por xmm1, xmm7
	add edx, 1
	movd xmm2, edx
	por xmm2, xmm7
	add edx, 1
	movd xmm3, edx
	por xmm3, xmm7
	add edx, 1
	movd xmm4, edx
	por xmm4, xmm7
	add edx, 1
	movd xmm5, edx
	por xmm5, xmm7
	add edx, 1
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 233f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 235f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 236f
235:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
236:
	jmp 234f
233:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
234:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 96
	cmp edi, 96
	jae 232b
	jmp 231f
230:
231:
	cmp edi, 16
	jb 237f
239:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 240f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 242f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 243f
242:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
243:
	jmp 241f
240:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
241:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	add edx, 1
	add esi, 16
	sub edi, 16
	cmp edi, 16
	jae 239b
	jmp 238f
237:
238:
	mov DWORD PTR [ebp+96], edx
	mov DWORD PTR [ebp+176], edi
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 244f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
246:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 246b
	jmp 245f
244:
245:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+172]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_open_aesni_pclmul:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov edi, DWORD PTR [ebp+172]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
	mov edx, DWORD PTR [ebp+96]
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edi, DWORD PTR [ebp+176]
	cmp edi, 96
	jb 23f
25:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	add edx, 1
	movd xmm1, edx
	por xmm1, xmm7
	add edx, 1
	movd xmm2, edx
	por xmm2, xmm7
	add edx, 1
	movd xmm3, edx
	por xmm3, xmm7
	add edx, 1
	movd xmm4, edx
	por xmm4, xmm7
	add edx, 1
	movd xmm5, edx
	por xmm5, xmm7
	add edx, 1
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 26f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 28f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 29f
28:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
29:
	jmp 27f
26:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
27:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 96
	cmp edi, 96
	jae 25b
	jmp 24f
23:
24:
	cmp edi, 16
	jb 210f
212:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 213f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 215f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 216f
215:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
216:
	jmp 214f
213:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
214:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	add edx, 1
	add esi, 16
	sub edi, 16
	cmp edi, 16
	jae 212b
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+96], edx
	mov DWORD PTR [ebp+176], edi
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 217f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
219:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 220f
222:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 223f
	mov ecx, 64
	jmp 224f
223:
224:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
225:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 225b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 222b
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 226f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 229f
	mov ecx, 64
	jmp 230f
229:
230:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
231:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 231b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 227f
226:
227:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 232f
234:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 235f
	mov ecx, 64
	jmp 236f
235:
236:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
237:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 237b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 234b
	jmp 233f
232:
233:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 238f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
240:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 240b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 241f
	mov ecx, 64
	jmp 242f
241:
242:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
243:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 243b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 239f
238:
239:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 244f
	mov ecx, 64
	jmp 245f
244:
245:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
246:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 246b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 240
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+244]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+248]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+252]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov ebx, 0
	sub ebx, eax
	mov ecx, DWORD PTR [ebp+168]
	test ecx, ecx
	je 247f
	mov edi, DWORD PTR [ebp+164]
	cmp ecx, 4
	jb 249f
251:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 251b
	jmp 250f
249:
250:
	test ecx, ecx
	je 252f
254:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 248f
247:
248:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_seal_aesni:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 24f
	mov ecx, 64
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
26:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
212:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 28f
27:
28:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 213f
215:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
218:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 215b
	jmp 214f
213:
214:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 219f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
224:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 225f
	mov ecx, 64
	jmp 226f
225:
226:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
227:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 227b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 228f
	mov edx, DWORD PTR [ebp+96]
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edi, DWORD PTR [ebp+176]
	cmp edi, 96
	jb 230f
232:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	add edx, 1
	movd xmm1, edx
	por xmm1, xmm7
	add edx, 1
	movd xmm2, edx
	por xmm2, xmm7
	add edx, 1
	movd xmm3, edx
	por xmm3, xmm7
	add edx, 1
	movd xmm4, edx
	por xmm4, xmm7
	add edx, 1
	movd xmm5, edx
	por xmm5, xmm7
	add edx, 1
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 233f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 235f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 236f
235:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
236:
	jmp 234f
233:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
234:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 96
	cmp edi, 96
	jae 232b
	jmp 231f
230:
231:
	cmp edi, 16
	jb 237f
239:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 240f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 242f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 243f
242:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
243:
	jmp 241f
240:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
241:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	add edx, 1
	add esi, 16
	sub edi, 16
	cmp edi, 16
	jae 239b
	jmp 238f
237:
238:
	mov DWORD PTR [ebp+96], edx
	mov DWORD PTR [ebp+176], edi
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 244f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
246:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 246b
	jmp 245f
244:
245:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+172]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_open_aesni:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov edi, DWORD PTR [ebp+172]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
	mov edx, DWORD PTR [ebp+96]
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edi, DWORD PTR [ebp+176]
	cmp edi, 96
	jb 23f
25:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	add edx, 1
	movd xmm1, edx
	por xmm1, xmm7
	add edx, 1
	movd xmm2, edx
	por xmm2, xmm7
	add edx, 1
	movd xmm3, edx
	por xmm3, xmm7
	add edx, 1
	movd xmm4, edx
	por xmm4, xmm7
	add edx, 1
	movd xmm5, edx
	por xmm5, xmm7
	add edx, 1
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 26f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 28f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 29f
28:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
29:
	jmp 27f
26:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
27:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 96
	cmp edi, 96
	jae 25b
	jmp 24f
23:
24:
	cmp edi, 16
	jb 210f
212:
	movdqu xmm7, XMMWORD PTR [ebp+96]
	movd xmm0, edx
	por xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 213f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 215f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 216f
215:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
216:
	jmp 214f
213:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
214:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	add edx, 1
	add esi, 16
	sub edi, 16
	cmp edi, 16
	jae 212b
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+96], edx
	mov DWORD PTR [ebp+176], edi
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 217f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
219:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 220f
222:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 223f
	mov ecx, 64
	jmp 224f
223:
224:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
225:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 225b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 222b
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 226f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 229f
	mov ecx, 64
	jmp 230f
229:
230:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
231:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 231b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 227f
226:
227:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 232f
234:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 235f
	mov ecx, 64
	jmp 236f
235:
236:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
237:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 237b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 234b
	jmp 233f
232:
233:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 238f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
240:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 240b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 241f
	mov ecx, 64
	jmp 242f
241:
242:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
243:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 243b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 239f
238:
239:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 244f
	mov ecx, 64
	jmp 245f
244:
245:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
246:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 246b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 240
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+244]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+248]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+252]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov ebx, 0
	sub ebx, eax
	mov ecx, DWORD PTR [ebp+168]
	test ecx, ecx
	je 247f
	mov edi, DWORD PTR [ebp+164]
	cmp ecx, 4
	jb 249f
251:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 251b
	jmp 250f
249:
250:
	test ecx, ecx
	je 252f
254:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 254b
	jmp 253f
252:
253:
	jmp 248f
247:
248:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_seal_pclmul:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 24f
	mov ecx, 64
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
26:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
212:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 28f
27:
28:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 213f
215:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
218:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 215b
	jmp 214f
213:
214:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 219f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
224:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 225f
	mov ecx, 64
	jmp 226f
225:
226:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
227:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 227b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 228f
230:
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, esi
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+96]
	add eax, 1
	mov DWORD PTR [ebp+96], eax
	add esi, 16
	mov eax, DWORD PTR [ebp+176]
	sub eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 230b
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 231f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
233:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 233b
	jmp 232f
231:
232:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+172]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_open_pclmul:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov edi, DWORD PTR [ebp+172]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, esi
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+96]
	add eax, 1
	mov DWORD PTR [ebp+96], eax
	add esi, 16
	mov eax, DWORD PTR [ebp+176]
	sub eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 24f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
26:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 27f
29:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
212:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 29b
	jmp 28f
27:
28:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 213f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
218:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 214f
213:
214:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 219f
221:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
224:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 221b
	jmp 220f
219:
220:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 225f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
227:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 228f
	mov ecx, 64
	jmp 229f
228:
229:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
230:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 230b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 226f
225:
226:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 231f
	mov ecx, 64
	jmp 232f
231:
232:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
233:
	movdqu xmm7, XMMWORD PTR [esi]
	pshufb xmm7, xmm0
	movdqu XMMWORD PTR [edx], xmm7
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 233b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash_pclmul}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 240
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+244]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+248]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+252]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov ebx, 0
	sub ebx, eax
	mov ecx, DWORD PTR [ebp+168]
	test ecx, ecx
	je 234f
	mov edi, DWORD PTR [ebp+164]
	cmp ecx, 4
	jb 236f
238:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 238b
	jmp 237f
236:
237:
	test ecx, ecx
	je 239f
241:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 241b
	jmp 240f
239:
240:
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_seal:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 24f
	mov ecx, 64
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
26:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
212:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 28f
27:
28:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 213f
215:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
218:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 215b
	jmp 214f
213:
214:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 219f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
221:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 221b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
224:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 220f
219:
220:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 225f
	mov ecx, 64
	jmp 226f
225:
226:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
227:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 227b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 228f
230:
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, esi
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+96]
	add eax, 1
	mov DWORD PTR [ebp+96], eax
	add esi, 16
	mov eax, DWORD PTR [ebp+176]
	sub eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 230b
	jmp 229f
228:
229:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 231f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
233:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 233b
	jmp 232f
231:
232:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [ebp+172]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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

vg_aes_gcm_siv_open:
	lea esp, [esp-2856]
	mov eax, DWORD PTR [esp+2860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2868]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2872]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2876]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2880]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2884]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2888]
	mov DWORD PTR [esp+32], eax
	mov eax, esp
	add eax, 40
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+172], eax
	mov edi, DWORD PTR [ebp+172]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, 0
	mov DWORD PTR [ebp+180], eax
20:
	mov eax, DWORD PTR [ebp+152]
	mov ecx, DWORD PTR [eax]
	mov edx, DWORD PTR [eax+4]
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [ebp+116], ecx
	mov DWORD PTR [ebp+120], edx
	mov DWORD PTR [ebp+124], ebx
	mov eax, DWORD PTR [ebp+180]
	mov DWORD PTR [ebp+112], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, DWORD PTR [ebp+180]
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, ebp
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+180]
	add eax, 1
	mov DWORD PTR [ebp+180], eax
	mov ecx, DWORD PTR [ebp+148]
	shr ecx, 1
	sub ecx, 1
	cmp eax, ecx
	jne 20b
	mov eax, ebp
	add eax, 32
	mov ecx, DWORD PTR [ebp+148]
	sub ecx, 6
	add ecx, ecx
	add ecx, ecx
	mov edx, ebp
	add edx, 512
	add ebp, 768
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+16]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+20]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+20]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+24]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+24]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+28]
	and ecx, 1
	ror ecx, 1
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+28]
	shr eax, 1
	mov ecx, DWORD PTR [ebp+16]
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	and edx, -520093696
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	or eax, -2147483648
	mov DWORD PTR [ebp+108], eax
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 21f
23:
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, esi
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp+96]
	add eax, 1
	mov DWORD PTR [ebp+96], eax
	add esi, 16
	mov eax, DWORD PTR [ebp+176]
	sub eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 23b
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 24f
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 224
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov edx, ebp
	add edx, 224
	mov edi, esi
	mov ecx, DWORD PTR [ebp+176]
26:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov esi, DWORD PTR [ebp+156]
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 27f
29:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 210f
	mov ecx, 64
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
212:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 212b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 29b
	jmp 28f
27:
28:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 213f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
215:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 215b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 216f
	mov ecx, 64
	jmp 217f
216:
217:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
218:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 218b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 214f
213:
214:
	mov esi, DWORD PTR [ebp+164]
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	je 219f
221:
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 222f
	mov ecx, 64
	jmp 223f
222:
223:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
224:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 224b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jne 221b
	jmp 220f
219:
220:
	mov ecx, DWORD PTR [ebp+176]
	test ecx, ecx
	je 225f
	mov eax, 0
	mov DWORD PTR [ebp+224], eax
	mov DWORD PTR [ebp+228], eax
	mov DWORD PTR [ebp+232], eax
	mov DWORD PTR [ebp+236], eax
	mov edi, esi
	mov edx, ebp
	add edx, 224
	mov ecx, DWORD PTR [ebp+176]
227:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 228f
	mov ecx, 64
	jmp 229f
228:
229:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
230:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 230b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	jmp 226f
225:
226:
	mov eax, DWORD PTR [ebp+160]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+160]
	shr eax, 29
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+168]
	add eax, eax
	add eax, eax
	add eax, eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+168]
	shr eax, 29
	mov DWORD PTR [ebp+236], eax
	mov esi, ebp
	add esi, 224
	mov eax, 16
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	cmp ecx, 64
	jb 231f
	mov ecx, 64
	jmp 232f
231:
232:
	mov DWORD PTR [ebp+180], ecx
	mov edx, ebp
	add edx, 768
233:
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [edx+12], eax
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 233b
	mov edi, DWORD PTR [ebp+180]
	mov eax, edi
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+176]
	sub ecx, eax
	mov DWORD PTR [ebp+176], ecx
	mov eax, ebp
	add eax, 64
	mov edx, ebp
	add edx, 80
	mov ebx, ebp
	add ebx, 768
	add ebp, 1792
	push ebp
	push edi
	push ebx
	push edx
	push eax
	call {vg_ghash}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 1792
	mov ecx, DWORD PTR [ebp+176]
	shr ecx, 4
	test ecx, ecx
	mov ecx, DWORD PTR [ebp+152]
	mov edx, DWORD PTR [ecx]
	mov ebx, DWORD PTR [ecx+4]
	mov edi, DWORD PTR [ecx+8]
	mov eax, DWORD PTR [ebp+92]
	bswap eax
	xor eax, edx
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+88]
	bswap eax
	xor eax, ebx
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+84]
	bswap eax
	xor eax, edi
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+80]
	bswap eax
	and eax, 2147483647
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+124], eax
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov eax, ebp
	add eax, 512
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 112
	mov ebx, ebp
	add ebx, 240
	mov edi, 1
	add ebp, 768
	push ebx
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_to}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 768
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+244]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+248]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+252]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov ebx, 0
	sub ebx, eax
	mov ecx, DWORD PTR [ebp+168]
	test ecx, ecx
	je 234f
	mov edi, DWORD PTR [ebp+164]
	cmp ecx, 4
	jb 236f
238:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 238b
	jmp 237f
236:
237:
	test ecx, ecx
	je 239f
241:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 241b
	jmp 240f
239:
240:
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2888]
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
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	movdqu XMMWORD PTR [esp+1424], xmm0
	movdqu XMMWORD PTR [esp+1440], xmm0
	movdqu XMMWORD PTR [esp+1456], xmm0
	movdqu XMMWORD PTR [esp+1472], xmm0
	movdqu XMMWORD PTR [esp+1488], xmm0
	movdqu XMMWORD PTR [esp+1504], xmm0
	movdqu XMMWORD PTR [esp+1520], xmm0
	movdqu XMMWORD PTR [esp+1536], xmm0
	movdqu XMMWORD PTR [esp+1552], xmm0
	movdqu XMMWORD PTR [esp+1568], xmm0
	movdqu XMMWORD PTR [esp+1584], xmm0
	movdqu XMMWORD PTR [esp+1600], xmm0
	movdqu XMMWORD PTR [esp+1616], xmm0
	movdqu XMMWORD PTR [esp+1632], xmm0
	movdqu XMMWORD PTR [esp+1648], xmm0
	movdqu XMMWORD PTR [esp+1664], xmm0
	movdqu XMMWORD PTR [esp+1680], xmm0
	movdqu XMMWORD PTR [esp+1696], xmm0
	movdqu XMMWORD PTR [esp+1712], xmm0
	movdqu XMMWORD PTR [esp+1728], xmm0
	movdqu XMMWORD PTR [esp+1744], xmm0
	movdqu XMMWORD PTR [esp+1760], xmm0
	movdqu XMMWORD PTR [esp+1776], xmm0
	movdqu XMMWORD PTR [esp+1792], xmm0
	movdqu XMMWORD PTR [esp+1808], xmm0
	movdqu XMMWORD PTR [esp+1824], xmm0
	movdqu XMMWORD PTR [esp+1840], xmm0
	movdqu XMMWORD PTR [esp+1856], xmm0
	movdqu XMMWORD PTR [esp+1872], xmm0
	movdqu XMMWORD PTR [esp+1888], xmm0
	movdqu XMMWORD PTR [esp+1904], xmm0
	movdqu XMMWORD PTR [esp+1920], xmm0
	movdqu XMMWORD PTR [esp+1936], xmm0
	movdqu XMMWORD PTR [esp+1952], xmm0
	movdqu XMMWORD PTR [esp+1968], xmm0
	movdqu XMMWORD PTR [esp+1984], xmm0
	movdqu XMMWORD PTR [esp+2000], xmm0
	movdqu XMMWORD PTR [esp+2016], xmm0
	movdqu XMMWORD PTR [esp+2032], xmm0
	movdqu XMMWORD PTR [esp+2048], xmm0
	movdqu XMMWORD PTR [esp+2064], xmm0
	movdqu XMMWORD PTR [esp+2080], xmm0
	movdqu XMMWORD PTR [esp+2096], xmm0
	movdqu XMMWORD PTR [esp+2112], xmm0
	movdqu XMMWORD PTR [esp+2128], xmm0
	movdqu XMMWORD PTR [esp+2144], xmm0
	movdqu XMMWORD PTR [esp+2160], xmm0
	movdqu XMMWORD PTR [esp+2176], xmm0
	movdqu XMMWORD PTR [esp+2192], xmm0
	movdqu XMMWORD PTR [esp+2208], xmm0
	movdqu XMMWORD PTR [esp+2224], xmm0
	movdqu XMMWORD PTR [esp+2240], xmm0
	movdqu XMMWORD PTR [esp+2256], xmm0
	movdqu XMMWORD PTR [esp+2272], xmm0
	movdqu XMMWORD PTR [esp+2288], xmm0
	movdqu XMMWORD PTR [esp+2304], xmm0
	movdqu XMMWORD PTR [esp+2320], xmm0
	movdqu XMMWORD PTR [esp+2336], xmm0
	movdqu XMMWORD PTR [esp+2352], xmm0
	movdqu XMMWORD PTR [esp+2368], xmm0
	movdqu XMMWORD PTR [esp+2384], xmm0
	movdqu XMMWORD PTR [esp+2400], xmm0
	movdqu XMMWORD PTR [esp+2416], xmm0
	movdqu XMMWORD PTR [esp+2432], xmm0
	movdqu XMMWORD PTR [esp+2448], xmm0
	movdqu XMMWORD PTR [esp+2464], xmm0
	movdqu XMMWORD PTR [esp+2480], xmm0
	movdqu XMMWORD PTR [esp+2496], xmm0
	movdqu XMMWORD PTR [esp+2512], xmm0
	movdqu XMMWORD PTR [esp+2528], xmm0
	movdqu XMMWORD PTR [esp+2544], xmm0
	movdqu XMMWORD PTR [esp+2560], xmm0
	movdqu XMMWORD PTR [esp+2576], xmm0
	movdqu XMMWORD PTR [esp+2592], xmm0
	movdqu XMMWORD PTR [esp+2608], xmm0
	movdqu XMMWORD PTR [esp+2624], xmm0
	movdqu XMMWORD PTR [esp+2640], xmm0
	movdqu XMMWORD PTR [esp+2656], xmm0
	movdqu XMMWORD PTR [esp+2672], xmm0
	movdqu XMMWORD PTR [esp+2688], xmm0
	movdqu XMMWORD PTR [esp+2704], xmm0
	movdqu XMMWORD PTR [esp+2720], xmm0
	movdqu XMMWORD PTR [esp+2736], xmm0
	movdqu XMMWORD PTR [esp+2752], xmm0
	movdqu XMMWORD PTR [esp+2768], xmm0
	movdqu XMMWORD PTR [esp+2784], xmm0
	movdqu XMMWORD PTR [esp+2800], xmm0
	movdqu XMMWORD PTR [esp+2816], xmm0
	movdqu XMMWORD PTR [esp+2832], xmm0
	movdqu XMMWORD PTR [esp+2848], xmm0
	movdqu XMMWORD PTR [esp+2864], xmm0
	mov DWORD PTR [esp+2880], ecx
	mov DWORD PTR [esp+2884], ecx
	lea esp, [esp+2888]
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
