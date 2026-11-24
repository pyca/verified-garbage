// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init_aesni:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, DWORD PTR [ebp+176]
	add ebp, 512
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edx, DWORD PTR [ebp+176]
	mov eax, 0
	mov DWORD PTR [edx+240], eax
	mov DWORD PTR [edx+244], eax
	mov DWORD PTR [edx+248], eax
	mov DWORD PTR [edx+252], eax
	mov eax, edx
	mov ecx, DWORD PTR [ebp+188]
	shr ecx, 2
	add ecx, 6
	add edx, 240
	mov ebx, 1
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2580]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2604]
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
	mov DWORD PTR [esp+2592], ecx
	mov DWORD PTR [esp+2596], ecx
	mov DWORD PTR [esp+2600], ecx
	lea esp, [esp+2604]
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

vg_aes_ocb_seal_aesni:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 6
	jb 226f
228:
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+768], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 237f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 239f
241:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 241b
	jmp 240f
239:
240:
	jmp 238f
237:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 242f
	jmp 243f
242:
244:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 244b
243:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
238:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+784], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 245f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 247f
249:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 249b
	jmp 248f
247:
248:
	jmp 246f
245:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 250f
	jmp 251f
250:
252:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 252b
251:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
246:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+800], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 253f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 255f
257:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 257b
	jmp 256f
255:
256:
	jmp 254f
253:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258f
	jmp 259f
258:
260:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 260b
259:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
254:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+816], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 261f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 263f
265:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 265b
	jmp 264f
263:
264:
	jmp 262f
261:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 266f
	jmp 267f
266:
268:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 268b
267:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
262:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+832], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 269f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 271f
273:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 273b
	jmp 272f
271:
272:
	jmp 270f
269:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 274f
	jmp 275f
274:
276:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 276b
275:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
270:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+848], xmm0
	add edi, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 512
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	movdqu xmm2, XMMWORD PTR [esi+16]
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebp+784]
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+32]
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebp+800]
	pxor xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+48]
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebp+816]
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [esi+64]
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebp+832]
	pxor xmm5, xmm6
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebp+848]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	cmp ecx, 10
	je 277f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	cmp ecx, 12
	je 279f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	aesenc xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	aesenclast xmm7, xmm6
	jmp 280f
279:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	aesenclast xmm7, xmm6
280:
	jmp 278f
277:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	aesenclast xmm7, xmm6
278:
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm6, XMMWORD PTR [ebp+784]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [esi+16], xmm2
	movdqu xmm6, XMMWORD PTR [ebp+800]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [esi+32], xmm3
	movdqu xmm6, XMMWORD PTR [ebp+816]
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [esi+48], xmm4
	movdqu xmm6, XMMWORD PTR [ebp+832]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [esi+64], xmm5
	movdqu xmm6, XMMWORD PTR [ebp+848]
	pxor xmm7, xmm6
	movdqu XMMWORD PTR [esi+80], xmm7
	movdqu xmm0, XMMWORD PTR [ebp+848]
	add esi, 96
	sub ebx, 6
	cmp ebx, 6
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 281f
283:
	mov eax, edi
	test eax, 63
	je 284f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 286f
288:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 288b
	jmp 287f
286:
287:
	jmp 285f
284:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 289f
	jmp 290f
289:
291:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 291b
290:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
285:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+768], xmm0
	add edi, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 512
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
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
	je 292f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 294f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 295f
294:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
295:
	jmp 293f
292:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
293:
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm0, XMMWORD PTR [ebp+768]
	add esi, 16
	sub ebx, 1
	jne 283b
	jmp 282f
281:
282:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 296f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
298:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 298b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
299:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 299b
	jmp 297f
296:
297:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+12], eax
	mov edi, ebp
	mov edx, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
2100:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 2100b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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

vg_aes_ocb_open_aesni:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 512
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+16], xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+32], xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+48], xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+64], xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+80], xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+96], xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+112], xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+128], xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+144], xmm6
	cmp ecx, 10
	je 226f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+160], xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+176], xmm6
	cmp ecx, 12
	je 228f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+192], xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesimc xmm6, xmm6
	movdqu XMMWORD PTR [edx+208], xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	movdqu XMMWORD PTR [edx+224], xmm6
	jmp 229f
228:
	movdqu xmm6, XMMWORD PTR [eax+192]
	movdqu XMMWORD PTR [edx+224], xmm6
229:
	jmp 227f
226:
	movdqu xmm6, XMMWORD PTR [eax+160]
	movdqu XMMWORD PTR [edx+224], xmm6
227:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 6
	jb 230f
232:
	mov eax, edi
	test eax, 63
	je 233f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 235f
237:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 237b
	jmp 236f
235:
236:
	jmp 234f
233:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 238f
	jmp 239f
238:
240:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 240b
239:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
234:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+768], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 241f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 243f
245:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 245b
	jmp 244f
243:
244:
	jmp 242f
241:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 246f
	jmp 247f
246:
248:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 248b
247:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
242:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+784], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 249f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 251f
253:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 253b
	jmp 252f
251:
252:
	jmp 250f
249:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 254f
	jmp 255f
254:
256:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256b
255:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
250:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+800], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 257f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 259f
261:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 261b
	jmp 260f
259:
260:
	jmp 258f
257:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 262f
	jmp 263f
262:
264:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 264b
263:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
258:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+816], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 265f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 267f
269:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 269b
	jmp 268f
267:
268:
	jmp 266f
265:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 270f
	jmp 271f
270:
272:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 272b
271:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
266:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+832], xmm0
	add edi, 1
	mov eax, edi
	test eax, 63
	je 273f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 275f
277:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 277b
	jmp 276f
275:
276:
	jmp 274f
273:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 278f
	jmp 279f
278:
280:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 280b
279:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
274:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+848], xmm0
	add edi, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 512
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [ebp+784]
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [ebp+800]
	pxor xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [ebp+816]
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [ebp+832]
	pxor xmm5, xmm6
	movdqu xmm7, XMMWORD PTR [esi+80]
	movdqu xmm6, XMMWORD PTR [ebp+848]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	pxor xmm7, xmm6
	cmp ecx, 10
	je 281f
	cmp ecx, 12
	je 283f
	movdqu xmm6, XMMWORD PTR [edx+208]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	jmp 284f
283:
284:
	movdqu xmm6, XMMWORD PTR [edx+176]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	jmp 282f
281:
282:
	movdqu xmm6, XMMWORD PTR [edx+144]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	aesdec xmm0, xmm6
	aesdec xmm2, xmm6
	aesdec xmm3, xmm6
	aesdec xmm4, xmm6
	aesdec xmm5, xmm6
	aesdec xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [eax]
	aesdeclast xmm0, xmm6
	aesdeclast xmm2, xmm6
	aesdeclast xmm3, xmm6
	aesdeclast xmm4, xmm6
	aesdeclast xmm5, xmm6
	aesdeclast xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm6, XMMWORD PTR [ebp+784]
	pxor xmm2, xmm6
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [esi+16], xmm2
	movdqu xmm6, XMMWORD PTR [ebp+800]
	pxor xmm3, xmm6
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi+32], xmm3
	movdqu xmm6, XMMWORD PTR [ebp+816]
	pxor xmm4, xmm6
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [esi+48], xmm4
	movdqu xmm6, XMMWORD PTR [ebp+832]
	pxor xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [esi+64], xmm5
	movdqu xmm6, XMMWORD PTR [ebp+848]
	pxor xmm7, xmm6
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+80], xmm7
	movdqu xmm0, XMMWORD PTR [ebp+848]
	add esi, 96
	sub ebx, 6
	cmp ebx, 6
	jae 232b
	jmp 231f
230:
231:
	test ebx, ebx
	je 285f
287:
	mov eax, edi
	test eax, 63
	je 288f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 290f
292:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 292b
	jmp 291f
290:
291:
	jmp 289f
288:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 293f
	jmp 294f
293:
295:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 295b
294:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
289:
	movdqu xmm6, XMMWORD PTR [edx]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [ebp+768], xmm0
	add edi, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 512
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pxor xmm0, xmm6
	cmp ecx, 10
	je 296f
	cmp ecx, 12
	je 298f
	movdqu xmm6, XMMWORD PTR [edx+208]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	aesdec xmm0, xmm6
	jmp 299f
298:
299:
	movdqu xmm6, XMMWORD PTR [edx+176]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	aesdec xmm0, xmm6
	jmp 297f
296:
297:
	movdqu xmm6, XMMWORD PTR [edx+144]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+96]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	aesdec xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax]
	aesdeclast xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [ebp+768]
	pxor xmm0, xmm6
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm0, XMMWORD PTR [ebp+768]
	add esi, 16
	sub ebx, 1
	jne 287b
	jmp 286f
285:
286:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 2100f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
2102:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 2102b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
2103:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 2103b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	jmp 2101f
2100:
2101:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+156], eax
	mov edi, DWORD PTR [ebp+208]
	mov edx, ebp
	mov ecx, DWORD PTR [ebp+212]
2104:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 2104b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
2105:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 2105b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	movd xmm0, edx
	pshufd xmm0, xmm0, 0
	mov eax, ecx
	shr eax, 4
	and ecx, 15
	test eax, eax
	je 2106f
2108:
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	add edi, 16
	sub eax, 1
	jne 2108b
	jmp 2107f
2106:
2107:
	test ecx, ecx
	je 2109f
2111:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 2111b
	jmp 2110f
2109:
2110:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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

vg_aes_ocb_init_ssse3:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, DWORD PTR [ebp+176]
	add ebp, 512
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edx, DWORD PTR [ebp+176]
	mov eax, 0
	mov DWORD PTR [edx+240], eax
	mov DWORD PTR [edx+244], eax
	mov DWORD PTR [edx+248], eax
	mov DWORD PTR [edx+252], eax
	mov eax, edx
	mov ecx, DWORD PTR [ebp+188]
	shr ecx, 2
	add ecx, 6
	add edx, 240
	mov ebx, 1
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2580]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2604]
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
	mov DWORD PTR [esp+2592], ecx
	mov DWORD PTR [esp+2596], ecx
	mov DWORD PTR [esp+2600], ecx
	lea esp, [esp+2604]
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

vg_aes_ocb_seal_ssse3:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+12], eax
	mov edi, ebp
	mov edx, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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

vg_aes_ocb_open_ssse3:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+156], eax
	mov edi, DWORD PTR [ebp+208]
	mov edx, ebp
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
275:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 275b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	movd xmm0, edx
	pshufd xmm0, xmm0, 0
	mov eax, ecx
	shr eax, 4
	and ecx, 15
	test eax, eax
	je 276f
278:
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	add edi, 16
	sub eax, 1
	jne 278b
	jmp 277f
276:
277:
	test ecx, ecx
	je 279f
281:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 281b
	jmp 280f
279:
280:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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

vg_aes_ocb_init:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, DWORD PTR [ebp+176]
	add ebp, 512
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edx, DWORD PTR [ebp+176]
	mov eax, 0
	mov DWORD PTR [edx+240], eax
	mov DWORD PTR [edx+244], eax
	mov DWORD PTR [edx+248], eax
	mov DWORD PTR [edx+252], eax
	mov eax, edx
	mov ecx, DWORD PTR [ebp+188]
	shr ecx, 2
	add ecx, 6
	add edx, 240
	mov ebx, 1
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2580]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2604]
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
	mov DWORD PTR [esp+2592], ecx
	mov DWORD PTR [esp+2596], ecx
	mov DWORD PTR [esp+2600], ecx
	lea esp, [esp+2604]
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

vg_aes_ocb_seal:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+12], eax
	mov edi, ebp
	mov edx, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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

vg_aes_ocb_open:
	lea esp, [esp-2608]
	mov eax, DWORD PTR [esp+2612]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+2644]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+2648]
	mov DWORD PTR [esp+40], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+156], eax
	mov edi, DWORD PTR [ebp+208]
	mov edx, ebp
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
275:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 275b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	movd xmm0, edx
	pshufd xmm0, xmm0, 0
	mov eax, ecx
	shr eax, 4
	and ecx, 15
	test eax, eax
	je 276f
278:
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	add edi, 16
	sub eax, 1
	jne 278b
	jmp 277f
276:
277:
	test ecx, ecx
	je 279f
281:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 281b
	jmp 280f
279:
280:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2632]
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
	mov DWORD PTR [esp+2624], ecx
	mov DWORD PTR [esp+2628], ecx
	lea esp, [esp+2632]
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
