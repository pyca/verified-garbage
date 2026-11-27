// The functions of `src/pbkdf2_sha512.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512:
	lea esp, [esp-3444]
	mov eax, DWORD PTR [esp+3448]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+3452]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+3456]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+3460]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+3464]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+3468]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+3472]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+1872], ebx
	mov DWORD PTR [eax+1876], esi
	mov DWORD PTR [eax+1880], edi
	mov DWORD PTR [eax+1884], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	cmp ecx, 129
	jae 20f
	mov edx, DWORD PTR [esp+4]
	jmp 21f
20:
	mov edi, ebp
	add edi, 2464
	push edi
	call {vg_sha512_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
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
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 2784
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
	add edx, 2784
	mov ecx, 64
21:
	mov edi, ebp
	add edi, 1888
	mov esi, ebp
	add esi, 2080
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
22:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+1888]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2272], dl
	add ecx, 1
	cmp ecx, 192
	jne 22b
	mov edi, ebp
	add edi, 2272
	mov eax, 0
	mov esi, 128
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
	mov eax, 1
	bswap eax
	mov DWORD PTR [ebp+2848], eax
	mov ebx, 0
	mov ecx, DWORD PTR [esp+28]
	test ecx, ecx
	je 23f
25:
	mov ecx, 0
26:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2272]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2464], dl
	add ecx, 1
	cmp ecx, 192
	jne 26b
	mov edi, ebp
	add edi, 2464
	mov esi, DWORD PTR [esp+16]
	add esi, 128
	mov eax, 0
	mov ecx, 4
	mov edx, ebp
	add edx, 2848
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
	mov edx, ebp
	add edx, 2464
	mov esi, ebp
	add esi, 2080
	mov eax, DWORD PTR [esp+16]
	add eax, 132
	mov ecx, 0
	mov edi, ebp
	add edi, 2656
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 0
27:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2656]
	mov eax, ebp
	add eax, ecx
	mov BYTE PTR [eax+2720], dl
	add ecx, 1
	cmp ecx, 64
	jne 27b
	mov esi, ebp
	add esi, 1888
	mov eax, ebp
	add eax, 2656
	mov ecx, DWORD PTR [esp+20]
	sub ecx, 1
	mov edx, ebp
	add edx, 2720
	push ebp
	push edx
	push ecx
	push eax
	push esi
	call {vg_pbkdf2_hmac_sha512_iterate}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+28]
	sub ecx, ebx
	cmp ecx, 64
	jb 28f
	mov ecx, 64
	jmp 29f
28:
29:
	mov esi, ecx
	mov edi, DWORD PTR [esp+24]
	add edi, ebx
	mov ecx, 0
210:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+2720]
	mov eax, edi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, esi
	jne 210b
	add ebx, esi
	mov eax, DWORD PTR [ebp+2848]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [ebp+2848], eax
	mov eax, DWORD PTR [esp+28]
	cmp ebx, eax
	jne 25b
	jmp 24f
23:
24:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+1872]
	mov esi, DWORD PTR [eax+1876]
	mov edi, DWORD PTR [eax+1880]
	mov ebp, DWORD PTR [eax+1884]
	lea esp, [esp+3444]
	pxor xmm0, xmm0
	lea esp, [esp-3520]
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
	movdqu XMMWORD PTR [esp+3504], xmm0
	lea esp, [esp+3520]
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
