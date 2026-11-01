// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
236:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 236b
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	ret
	.p2align 6

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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
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
236:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 236b
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
236:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 236b
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
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
236:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 236b
	jmp 235f
234:
235:
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2856]
	ret
	.p2align 6
