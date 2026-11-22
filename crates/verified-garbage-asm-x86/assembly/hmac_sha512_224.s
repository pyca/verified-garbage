// The functions of `src/hmac_sha512_224.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_init:
	mov eax, DWORD PTR [esp+16]
	cmp eax, 129
	jae 20f
	lea esp, [esp-1896]
	mov eax, DWORD PTR [esp+1900]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1904]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1908]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1912]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_sha512_224_init_core}
	pop eax
	push esi
	call {vg_sha512_224_init_core}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov DWORD PTR [ebx+80], ecx
	mov DWORD PTR [ebx+84], ecx
	mov DWORD PTR [ebx+88], ecx
	mov DWORD PTR [ebx+92], ecx
	mov DWORD PTR [ebx+96], ecx
	mov DWORD PTR [ebx+100], ecx
	mov DWORD PTR [ebx+104], ecx
	mov DWORD PTR [ebx+108], ecx
	mov DWORD PTR [ebx+112], ecx
	mov DWORD PTR [ebx+116], ecx
	mov DWORD PTR [ebx+120], ecx
	mov DWORD PTR [ebx+124], ecx
	mov DWORD PTR [ebx+128], ecx
	mov DWORD PTR [ebx+132], ecx
	mov DWORD PTR [ebx+136], ecx
	mov DWORD PTR [ebx+140], ecx
	mov DWORD PTR [ebx+144], ecx
	mov DWORD PTR [ebx+148], ecx
	mov DWORD PTR [ebx+152], ecx
	mov DWORD PTR [ebx+156], ecx
	mov DWORD PTR [ebx+160], ecx
	mov DWORD PTR [ebx+164], ecx
	mov DWORD PTR [ebx+168], ecx
	mov DWORD PTR [ebx+172], ecx
	mov DWORD PTR [ebx+176], ecx
	mov DWORD PTR [ebx+180], ecx
	mov DWORD PTR [ebx+184], ecx
	mov DWORD PTR [ebx+188], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 64
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [edi]
	xor eax, 54
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [ebx+64]
	xor eax, 1785358954
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [ebx+68]
	xor eax, 1785358954
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [ebx+72]
	xor eax, 1785358954
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [ebx+76]
	xor eax, 1785358954
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [ebx+80]
	xor eax, 1785358954
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [ebx+84]
	xor eax, 1785358954
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [ebx+88]
	xor eax, 1785358954
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [ebx+92]
	xor eax, 1785358954
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [ebx+96]
	xor eax, 1785358954
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [ebx+100]
	xor eax, 1785358954
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [ebx+104]
	xor eax, 1785358954
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [ebx+108]
	xor eax, 1785358954
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [ebx+112]
	xor eax, 1785358954
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [ebx+116]
	xor eax, 1785358954
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [ebx+120]
	xor eax, 1785358954
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [ebx+124]
	xor eax, 1785358954
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [ebx+128]
	xor eax, 1785358954
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [ebx+132]
	xor eax, 1785358954
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [ebx+136]
	xor eax, 1785358954
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [ebx+140]
	xor eax, 1785358954
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [ebx+144]
	xor eax, 1785358954
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [ebx+148]
	xor eax, 1785358954
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [ebx+152]
	xor eax, 1785358954
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [ebx+156]
	xor eax, 1785358954
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [ebx+160]
	xor eax, 1785358954
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [ebx+164]
	xor eax, 1785358954
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [ebx+168]
	xor eax, 1785358954
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [ebx+172]
	xor eax, 1785358954
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [ebx+176]
	xor eax, 1785358954
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [ebx+180]
	xor eax, 1785358954
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [ebx+184]
	xor eax, 1785358954
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [ebx+188]
	xor eax, 1785358954
	mov DWORD PTR [esi+188], eax
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	lea esp, [esp+1896]
21:
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-3508]
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
	movdqu XMMWORD PTR [esp+2880], xmm0
	movdqu XMMWORD PTR [esp+2896], xmm0
	movdqu XMMWORD PTR [esp+2912], xmm0
	movdqu XMMWORD PTR [esp+2928], xmm0
	movdqu XMMWORD PTR [esp+2944], xmm0
	movdqu XMMWORD PTR [esp+2960], xmm0
	movdqu XMMWORD PTR [esp+2976], xmm0
	movdqu XMMWORD PTR [esp+2992], xmm0
	movdqu XMMWORD PTR [esp+3008], xmm0
	movdqu XMMWORD PTR [esp+3024], xmm0
	movdqu XMMWORD PTR [esp+3040], xmm0
	movdqu XMMWORD PTR [esp+3056], xmm0
	movdqu XMMWORD PTR [esp+3072], xmm0
	movdqu XMMWORD PTR [esp+3088], xmm0
	movdqu XMMWORD PTR [esp+3104], xmm0
	movdqu XMMWORD PTR [esp+3120], xmm0
	movdqu XMMWORD PTR [esp+3136], xmm0
	movdqu XMMWORD PTR [esp+3152], xmm0
	movdqu XMMWORD PTR [esp+3168], xmm0
	movdqu XMMWORD PTR [esp+3184], xmm0
	movdqu XMMWORD PTR [esp+3200], xmm0
	movdqu XMMWORD PTR [esp+3216], xmm0
	movdqu XMMWORD PTR [esp+3232], xmm0
	movdqu XMMWORD PTR [esp+3248], xmm0
	movdqu XMMWORD PTR [esp+3264], xmm0
	movdqu XMMWORD PTR [esp+3280], xmm0
	movdqu XMMWORD PTR [esp+3296], xmm0
	movdqu XMMWORD PTR [esp+3312], xmm0
	movdqu XMMWORD PTR [esp+3328], xmm0
	movdqu XMMWORD PTR [esp+3344], xmm0
	movdqu XMMWORD PTR [esp+3360], xmm0
	movdqu XMMWORD PTR [esp+3376], xmm0
	movdqu XMMWORD PTR [esp+3392], xmm0
	movdqu XMMWORD PTR [esp+3408], xmm0
	movdqu XMMWORD PTR [esp+3424], xmm0
	movdqu XMMWORD PTR [esp+3440], xmm0
	movdqu XMMWORD PTR [esp+3456], xmm0
	movdqu XMMWORD PTR [esp+3472], xmm0
	movdqu XMMWORD PTR [esp+3488], xmm0
	mov DWORD PTR [esp+3504], ecx
	lea esp, [esp+3508]
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
20:
	lea esp, [esp-3432]
	mov eax, DWORD PTR [esp+3436]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3440]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3444]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3448]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1872], ebx
	mov DWORD PTR [eax+1876], esi
	mov DWORD PTR [eax+1880], edi
	mov DWORD PTR [eax+1884], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	cmp ecx, 129
	jae 25f
	mov edx, DWORD PTR [esp+12]
	jmp 26f
25:
	mov edi, ebp
	add edi, 2464
	push edi
	call {vg_sha512_224_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov edx, ebp
	add edx, 2712
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 2712
	mov ecx, 28
26:
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_224_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+1872]
	mov esi, DWORD PTR [eax+1876]
	mov edi, DWORD PTR [eax+1880]
	mov ebp, DWORD PTR [eax+1884]
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
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	movdqu XMMWORD PTR [esp+968], xmm0
	movdqu XMMWORD PTR [esp+984], xmm0
	movdqu XMMWORD PTR [esp+1000], xmm0
	movdqu XMMWORD PTR [esp+1016], xmm0
	movdqu XMMWORD PTR [esp+1032], xmm0
	movdqu XMMWORD PTR [esp+1048], xmm0
	movdqu XMMWORD PTR [esp+1064], xmm0
	movdqu XMMWORD PTR [esp+1080], xmm0
	movdqu XMMWORD PTR [esp+1096], xmm0
	movdqu XMMWORD PTR [esp+1112], xmm0
	movdqu XMMWORD PTR [esp+1128], xmm0
	movdqu XMMWORD PTR [esp+1144], xmm0
	movdqu XMMWORD PTR [esp+1160], xmm0
	movdqu XMMWORD PTR [esp+1176], xmm0
	movdqu XMMWORD PTR [esp+1192], xmm0
	movdqu XMMWORD PTR [esp+1208], xmm0
	movdqu XMMWORD PTR [esp+1224], xmm0
	movdqu XMMWORD PTR [esp+1240], xmm0
	movdqu XMMWORD PTR [esp+1256], xmm0
	movdqu XMMWORD PTR [esp+1272], xmm0
	movdqu XMMWORD PTR [esp+1288], xmm0
	movdqu XMMWORD PTR [esp+1304], xmm0
	movdqu XMMWORD PTR [esp+1320], xmm0
	movdqu XMMWORD PTR [esp+1336], xmm0
	movdqu XMMWORD PTR [esp+1352], xmm0
	movdqu XMMWORD PTR [esp+1368], xmm0
	movdqu XMMWORD PTR [esp+1384], xmm0
	movdqu XMMWORD PTR [esp+1400], xmm0
	movdqu XMMWORD PTR [esp+1416], xmm0
	movdqu XMMWORD PTR [esp+1432], xmm0
	movdqu XMMWORD PTR [esp+1448], xmm0
	movdqu XMMWORD PTR [esp+1464], xmm0
	movdqu XMMWORD PTR [esp+1480], xmm0
	movdqu XMMWORD PTR [esp+1496], xmm0
	movdqu XMMWORD PTR [esp+1512], xmm0
	movdqu XMMWORD PTR [esp+1528], xmm0
	movdqu XMMWORD PTR [esp+1544], xmm0
	movdqu XMMWORD PTR [esp+1560], xmm0
	movdqu XMMWORD PTR [esp+1576], xmm0
	movdqu XMMWORD PTR [esp+1592], xmm0
	movdqu XMMWORD PTR [esp+1608], xmm0
	movdqu XMMWORD PTR [esp+1624], xmm0
	movdqu XMMWORD PTR [esp+1640], xmm0
	movdqu XMMWORD PTR [esp+1656], xmm0
	movdqu XMMWORD PTR [esp+1672], xmm0
	movdqu XMMWORD PTR [esp+1688], xmm0
	movdqu XMMWORD PTR [esp+1704], xmm0
	movdqu XMMWORD PTR [esp+1720], xmm0
	movdqu XMMWORD PTR [esp+1736], xmm0
	movdqu XMMWORD PTR [esp+1752], xmm0
	movdqu XMMWORD PTR [esp+1768], xmm0
	movdqu XMMWORD PTR [esp+1784], xmm0
	movdqu XMMWORD PTR [esp+1800], xmm0
	movdqu XMMWORD PTR [esp+1816], xmm0
	movdqu XMMWORD PTR [esp+1832], xmm0
	movdqu XMMWORD PTR [esp+1848], xmm0
	movdqu XMMWORD PTR [esp+1864], xmm0
	movdqu XMMWORD PTR [esp+1880], xmm0
	movdqu XMMWORD PTR [esp+1896], xmm0
	movdqu XMMWORD PTR [esp+1912], xmm0
	movdqu XMMWORD PTR [esp+1928], xmm0
	movdqu XMMWORD PTR [esp+1944], xmm0
	movdqu XMMWORD PTR [esp+1960], xmm0
	movdqu XMMWORD PTR [esp+1976], xmm0
	movdqu XMMWORD PTR [esp+1992], xmm0
	movdqu XMMWORD PTR [esp+2008], xmm0
	movdqu XMMWORD PTR [esp+2024], xmm0
	movdqu XMMWORD PTR [esp+2040], xmm0
	movdqu XMMWORD PTR [esp+2056], xmm0
	movdqu XMMWORD PTR [esp+2072], xmm0
	movdqu XMMWORD PTR [esp+2088], xmm0
	movdqu XMMWORD PTR [esp+2104], xmm0
	movdqu XMMWORD PTR [esp+2120], xmm0
	movdqu XMMWORD PTR [esp+2136], xmm0
	movdqu XMMWORD PTR [esp+2152], xmm0
	movdqu XMMWORD PTR [esp+2168], xmm0
	movdqu XMMWORD PTR [esp+2184], xmm0
	movdqu XMMWORD PTR [esp+2200], xmm0
	movdqu XMMWORD PTR [esp+2216], xmm0
	movdqu XMMWORD PTR [esp+2232], xmm0
	movdqu XMMWORD PTR [esp+2248], xmm0
	movdqu XMMWORD PTR [esp+2264], xmm0
	movdqu XMMWORD PTR [esp+2280], xmm0
	movdqu XMMWORD PTR [esp+2296], xmm0
	movdqu XMMWORD PTR [esp+2312], xmm0
	movdqu XMMWORD PTR [esp+2328], xmm0
	movdqu XMMWORD PTR [esp+2344], xmm0
	movdqu XMMWORD PTR [esp+2360], xmm0
	movdqu XMMWORD PTR [esp+2376], xmm0
	movdqu XMMWORD PTR [esp+2392], xmm0
	movdqu XMMWORD PTR [esp+2408], xmm0
	movdqu XMMWORD PTR [esp+2424], xmm0
	movdqu XMMWORD PTR [esp+2440], xmm0
	movdqu XMMWORD PTR [esp+2456], xmm0
	movdqu XMMWORD PTR [esp+2472], xmm0
	movdqu XMMWORD PTR [esp+2488], xmm0
	movdqu XMMWORD PTR [esp+2504], xmm0
	movdqu XMMWORD PTR [esp+2520], xmm0
	movdqu XMMWORD PTR [esp+2536], xmm0
	movdqu XMMWORD PTR [esp+2552], xmm0
	movdqu XMMWORD PTR [esp+2568], xmm0
	movdqu XMMWORD PTR [esp+2584], xmm0
	movdqu XMMWORD PTR [esp+2600], xmm0
	movdqu XMMWORD PTR [esp+2616], xmm0
	movdqu XMMWORD PTR [esp+2632], xmm0
	movdqu XMMWORD PTR [esp+2648], xmm0
	movdqu XMMWORD PTR [esp+2664], xmm0
	movdqu XMMWORD PTR [esp+2680], xmm0
	movdqu XMMWORD PTR [esp+2696], xmm0
	movdqu XMMWORD PTR [esp+2712], xmm0
	movdqu XMMWORD PTR [esp+2728], xmm0
	movdqu XMMWORD PTR [esp+2744], xmm0
	movdqu XMMWORD PTR [esp+2760], xmm0
	movdqu XMMWORD PTR [esp+2776], xmm0
	movdqu XMMWORD PTR [esp+2792], xmm0
	movdqu XMMWORD PTR [esp+2808], xmm0
	movdqu XMMWORD PTR [esp+2824], xmm0
	movdqu XMMWORD PTR [esp+2840], xmm0
	movdqu XMMWORD PTR [esp+2856], xmm0
	movdqu XMMWORD PTR [esp+2872], xmm0
	movdqu XMMWORD PTR [esp+2888], xmm0
	movdqu XMMWORD PTR [esp+2904], xmm0
	movdqu XMMWORD PTR [esp+2920], xmm0
	movdqu XMMWORD PTR [esp+2936], xmm0
	movdqu XMMWORD PTR [esp+2952], xmm0
	movdqu XMMWORD PTR [esp+2968], xmm0
	movdqu XMMWORD PTR [esp+2984], xmm0
	movdqu XMMWORD PTR [esp+3000], xmm0
	movdqu XMMWORD PTR [esp+3016], xmm0
	movdqu XMMWORD PTR [esp+3032], xmm0
	movdqu XMMWORD PTR [esp+3048], xmm0
	movdqu XMMWORD PTR [esp+3064], xmm0
	movdqu XMMWORD PTR [esp+3080], xmm0
	movdqu XMMWORD PTR [esp+3096], xmm0
	movdqu XMMWORD PTR [esp+3112], xmm0
	movdqu XMMWORD PTR [esp+3128], xmm0
	movdqu XMMWORD PTR [esp+3144], xmm0
	movdqu XMMWORD PTR [esp+3160], xmm0
	movdqu XMMWORD PTR [esp+3176], xmm0
	movdqu XMMWORD PTR [esp+3192], xmm0
	movdqu XMMWORD PTR [esp+3208], xmm0
	movdqu XMMWORD PTR [esp+3224], xmm0
	movdqu XMMWORD PTR [esp+3240], xmm0
	movdqu XMMWORD PTR [esp+3256], xmm0
	movdqu XMMWORD PTR [esp+3272], xmm0
	movdqu XMMWORD PTR [esp+3288], xmm0
	movdqu XMMWORD PTR [esp+3304], xmm0
	movdqu XMMWORD PTR [esp+3320], xmm0
	movdqu XMMWORD PTR [esp+3336], xmm0
	movdqu XMMWORD PTR [esp+3352], xmm0
	movdqu XMMWORD PTR [esp+3368], xmm0
	movdqu XMMWORD PTR [esp+3384], xmm0
	movdqu XMMWORD PTR [esp+3400], xmm0
	movdqu XMMWORD PTR [esp+3416], xmm0
	lea esp, [esp+3432]
	jmp 21b
	.p2align 6

vg_hmac_sha512_224_finalize:
	lea esp, [esp-1900]
	mov eax, DWORD PTR [esp+1904]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1908]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1912]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1916]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1920]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 288
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [esi+20]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [esi+24]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [esi+28]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [esi+32]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [esi+36]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, DWORD PTR [esi+40]
	mov DWORD PTR [ebx+40], ecx
	mov ecx, DWORD PTR [esi+44]
	mov DWORD PTR [ebx+44], ecx
	mov ecx, DWORD PTR [esi+48]
	mov DWORD PTR [ebx+48], ecx
	mov ecx, DWORD PTR [esi+52]
	mov DWORD PTR [ebx+52], ecx
	mov ecx, DWORD PTR [esi+56]
	mov DWORD PTR [ebx+56], ecx
	mov ecx, DWORD PTR [esi+60]
	mov DWORD PTR [ebx+60], ecx
	mov ecx, DWORD PTR [ebp+288]
	mov DWORD PTR [ebx+64], ecx
	mov ecx, DWORD PTR [ebp+292]
	mov DWORD PTR [ebx+68], ecx
	mov ecx, DWORD PTR [ebp+296]
	mov DWORD PTR [ebx+72], ecx
	mov ecx, DWORD PTR [ebp+300]
	mov DWORD PTR [ebx+76], ecx
	mov ecx, DWORD PTR [ebp+304]
	mov DWORD PTR [ebx+80], ecx
	mov ecx, DWORD PTR [ebp+308]
	mov DWORD PTR [ebx+84], ecx
	mov ecx, DWORD PTR [ebp+312]
	mov DWORD PTR [ebx+88], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+92], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+100], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+104], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+108], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+124], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+128], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+132], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+136], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+140], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+144], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+148], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+152], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+156], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+160], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+164], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+168], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+172], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+176], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+180], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+184], ecx
	mov ecx, -536608768
	mov DWORD PTR [ebx+188], ecx
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 64
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ecx, DWORD PTR [ebx+64]
	mov DWORD PTR [edi], ecx
	mov ecx, DWORD PTR [ebx+68]
	mov DWORD PTR [edi+4], ecx
	mov ecx, DWORD PTR [ebx+72]
	mov DWORD PTR [edi+8], ecx
	mov ecx, DWORD PTR [ebx+76]
	mov DWORD PTR [edi+12], ecx
	mov ecx, DWORD PTR [ebx+80]
	mov DWORD PTR [edi+16], ecx
	mov ecx, DWORD PTR [ebx+84]
	mov DWORD PTR [edi+20], ecx
	mov ecx, DWORD PTR [ebx+88]
	mov DWORD PTR [edi+24], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	lea esp, [esp+1900]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1948]
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
	mov DWORD PTR [esp+1936], ecx
	mov DWORD PTR [esp+1940], ecx
	mov DWORD PTR [esp+1944], ecx
	lea esp, [esp+1948]
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
