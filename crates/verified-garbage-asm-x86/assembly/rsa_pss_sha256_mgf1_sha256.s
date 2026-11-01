// The functions of `src/rsa_pss_sha256_mgf1_sha256.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha256_mgf1_sha256_verify_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+200]
	mov edx, DWORD PTR [esp+192]
	mov edi, DWORD PTR [esp+196]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+132], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+80], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+84], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+88], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 20f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+204]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+80]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+84]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov esi, ebp
	add esi, 2048
	mov ecx, 64
	mov eax, 0
23:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 23b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	mov ebx, ebp
	add ebx, 2048
	mov ecx, 32
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+2080], eax
	mov eax, 36
	mov DWORD PTR [esp+92], eax
	mov eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
25:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 25b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
26:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 26b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
27:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
28:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 28b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
29:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 27b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+88]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 32
	sbb edx, edx
	and eax, edx
	add eax, 32
	mov ecx, eax
210:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 210b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 32
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+88]
	jb 22b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+84]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
211:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov ebp, DWORD PTR [esp+200]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+88]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+192]
	mov ecx, DWORD PTR [esp+132]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+132]
	test eax, eax
	je 212f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
214:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 214b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+88]
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
217:
	mov esi, ebp
	add esi, 2088
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+88]
218:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 218b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 217b
	mov eax, DWORD PTR [esp+88]
	sub eax, DWORD PTR [esp+116]
	add eax, 39
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+88]
	add eax, 47
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
219:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 219b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
220:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 220b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
221:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
222:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 222b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
223:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 223b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 221b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+88]
	mov edx, 0
	mov ecx, 32
224:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 213f
212:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
225:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 225b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
226:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 226b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	sub esi, DWORD PTR [esp+192]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+192]
	test ecx, ecx
	je 227f
229:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 229b
	jmp 228f
227:
228:
	mov eax, DWORD PTR [esp+192]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
230:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 230b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
231:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 231b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
232:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
233:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 233b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
234:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 234b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 232b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+88]
	mov edx, 0
	mov ecx, 32
235:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 235b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
213:
	jmp 21f
20:
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_pss_sha256_mgf1_sha256_verify_precomputed_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+200]
	mov edx, DWORD PTR [esp+192]
	mov edi, DWORD PTR [esp+196]
	mov eax, 0
	cmp eax, edi
	sbb eax, eax
	mov ebx, eax
	and ebx, 1
	mov DWORD PTR [esp+132], ebx
	xor eax, -1
	and edx, eax
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+168]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+80], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+84], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+88], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 20f
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+204]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov esi, ebp
	add esi, 1024
	mov edi, esi
	add edi, DWORD PTR [esp+168]
	sub edi, 1
	mov ebx, esi
	add ebx, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [edi]
	xor eax, 188
	movzx edx, BYTE PTR [esi]
	mov ecx, 0
	sub ecx, DWORD PTR [esp+80]
	and edx, ecx
	or eax, edx
	movzx edx, BYTE PTR [ebx]
	mov ecx, DWORD PTR [esp+84]
	xor ecx, 255
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov esi, ebp
	add esi, 2048
	mov ecx, 64
	mov eax, 0
23:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 23b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	mov ebx, ebp
	add ebx, 2048
	mov ecx, 32
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+2080], eax
	mov eax, 36
	mov DWORD PTR [esp+92], eax
	mov eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
25:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 25b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
26:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 26b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
27:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
28:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 28b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
29:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 27b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+88]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 32
	sbb edx, edx
	and eax, edx
	add eax, 32
	mov ecx, eax
210:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 210b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 32
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+88]
	jb 22b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+84]
	mov BYTE PTR [esi], al
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+88]
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
211:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov ebp, DWORD PTR [esp+200]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov edx, DWORD PTR [esp+88]
	sub edx, DWORD PTR [esp+116]
	sub edx, 1
	xor edx, DWORD PTR [esp+192]
	mov ecx, DWORD PTR [esp+132]
	sub ecx, 1
	and edx, ecx
	or eax, edx
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [esp+132]
	test eax, eax
	je 212f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
214:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 214b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+88]
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
217:
	mov esi, ebp
	add esi, 2088
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, DWORD PTR [esp+88]
218:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 218b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 217b
	mov eax, DWORD PTR [esp+88]
	sub eax, DWORD PTR [esp+116]
	add eax, 39
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+88]
	add eax, 47
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
219:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 219b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
220:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 220b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
221:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
222:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 222b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
223:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 223b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 221b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+88]
	mov edx, 0
	mov ecx, 32
224:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
	jmp 213f
212:
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
225:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 225b
	mov esi, DWORD PTR [esp+180]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
226:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 226b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	sub esi, DWORD PTR [esp+192]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+192]
	test ecx, ecx
	je 227f
229:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 229b
	jmp 228f
227:
228:
	mov eax, DWORD PTR [esp+192]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
230:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 230b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
231:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 231b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
232:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
233:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 233b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
234:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 234b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 232b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 832
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+88]
	mov edx, 0
	mov ecx, 32
235:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 235b
	mov eax, DWORD PTR [esp+112]
	or eax, edx
	cmp eax, 1
	sbb eax, eax
	and eax, 1
213:
	jmp 21f
20:
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_pss_sha256_mgf1_sha256_sign:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+240]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+236]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+80], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+84], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+88], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov esi, DWORD PTR [esp+232]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+236]
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [esp+236]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
27:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 27b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
28:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 28b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
29:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 210b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 29b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+80]
	add ebx, DWORD PTR [esp+88]
	sub ebx, DWORD PTR [esp+236]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	test ecx, ecx
	je 213f
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	jmp 214f
213:
214:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+80]
	add ebx, DWORD PTR [esp+88]
	mov ecx, 32
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
217:
	mov esi, ebp
	add esi, 2048
	mov ecx, 64
	mov eax, 0
218:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 218b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	mov ebx, ebp
	add ebx, 2048
	mov ecx, 32
219:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 219b
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+2080], eax
	mov eax, 36
	mov DWORD PTR [esp+92], eax
	mov eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
220:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 220b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
221:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 221b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
222:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
223:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 223b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
224:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 222b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+88]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 32
	sbb edx, edx
	and eax, edx
	add eax, 32
	mov ecx, eax
225:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 32
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+88]
	jb 217b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+84]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+244]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
226:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 226b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_pss_sha256_mgf1_sha256_sign_sha256_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+240]
	mov esi, DWORD PTR [esp+172]
	mov ecx, DWORD PTR [esp+176]
	mov edx, DWORD PTR [esp+236]
	movzx eax, BYTE PTR [esi]
	mov ebx, eax
	shr ebx, 1
	mov edi, ebx
	shr edi, 1
	or ebx, edi
	mov edi, ebx
	shr edi, 2
	or ebx, edi
	mov edi, ebx
	shr edi, 4
	or ebx, edi
	mov edi, ebx
	sub edi, 1
	shr edi, 31
	mov DWORD PTR [esp+80], edi
	mov esi, 0
	sub esi, edi
	and esi, 255
	or ebx, esi
	mov DWORD PTR [esp+84], ebx
	mov esi, ecx
	sub esi, edi
	sub esi, 33
	mov DWORD PTR [esp+88], esi
	mov ebx, eax
	sub ebx, 1
	shr ebx, 31
	mov edi, esi
	sub edi, 1
	shr edi, 31
	or ebx, edi
	sub esi, 1
	sub esi, edx
	shr esi, 31
	or ebx, esi
	mov esi, edx
	shr esi, 31
	or ebx, esi
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+228]
	mov ebx, ebp
	add ebx, 2056
	mov ecx, 32
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov esi, DWORD PTR [esp+232]
	mov ebx, ebp
	add ebx, 2088
	mov ecx, DWORD PTR [esp+236]
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [esp+236]
	add eax, 40
	mov DWORD PTR [esp+92], eax
	add eax, 8
	shr eax, 6
	add eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
27:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 27b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
28:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 28b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
29:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 210b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 29b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+80]
	add ebx, DWORD PTR [esp+88]
	sub ebx, DWORD PTR [esp+236]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	test ecx, ecx
	je 213f
215:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 215b
	jmp 214f
213:
214:
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+80]
	add ebx, DWORD PTR [esp+88]
	mov ecx, 32
216:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 216b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+176]
	sub esi, 1
	mov eax, 188
	mov BYTE PTR [esi], al
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
217:
	mov esi, ebp
	add esi, 2048
	mov ecx, 64
	mov eax, 0
218:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 218b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	add esi, DWORD PTR [esp+88]
	mov ebx, ebp
	add ebx, 2048
	mov ecx, 32
219:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 219b
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+2080], eax
	mov eax, 36
	mov DWORD PTR [esp+92], eax
	mov eax, 1
	mov DWORD PTR [esp+96], eax
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha256_init}
	pop eax
	mov esi, ebp
	add esi, 896
	mov ecx, 64
	mov eax, 0
220:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 220b
	mov ebx, ebp
	add ebx, 896
	mov eax, DWORD PTR [esp+92]
	mov ecx, 0
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+56], ecx
	bswap eax
	mov DWORD PTR [ebx+60], eax
	mov eax, DWORD PTR [esp+92]
	add eax, 8
	shr eax, 6
	mov DWORD PTR [esp+136], eax
	mov esi, ebp
	add esi, 2048
	mov edi, 0
	mov ebx, DWORD PTR [esp+96]
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
221:
	movzx eax, BYTE PTR [esi]
	mov edx, edi
	xor edx, DWORD PTR [esp+92]
	sub edx, 1
	sbb edx, edx
	and edx, 128
	or eax, edx
	mov edx, edi
	shr edx, 6
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, edi
	and ecx, 63
	add ecx, ebp
	movzx ecx, BYTE PTR [ecx+896]
	and ecx, edx
	or eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ebx, 1
	jne 221b
	mov eax, 0
	mov DWORD PTR [esp+100], eax
222:
	mov esi, DWORD PTR [esp+100]
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, esi
	add esi, ebp
	add esi, 2048
	mov ebx, ebp
	add ebx, 544
	mov ecx, 64
223:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 223b
	mov ebx, ebp
	add ebx, 512
	mov eax, ebp
	add eax, 544
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 512
	mov edi, ebp
	add edi, 768
	mov edx, DWORD PTR [esp+100]
	xor edx, DWORD PTR [esp+136]
	sub edx, 1
	sbb edx, edx
	mov ecx, 32
224:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	mov BYTE PTR [edi], bl
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [esp+100]
	add eax, 1
	mov DWORD PTR [esp+100], eax
	cmp eax, DWORD PTR [esp+96]
	jne 222b
	mov ebx, ebp
	add ebx, 768
	mov eax, ebp
	add eax, 832
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov edi, ebp
	add edi, 1024
	add edi, DWORD PTR [esp+80]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+88]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 32
	sbb edx, edx
	and eax, edx
	add eax, 32
	mov ecx, eax
225:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 225b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 32
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+88]
	jb 217b
	mov esi, ebp
	add esi, 1024
	add esi, DWORD PTR [esp+80]
	movzx eax, BYTE PTR [esi]
	and eax, DWORD PTR [esp+84]
	mov BYTE PTR [esi], al
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+244]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
226:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 226b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
