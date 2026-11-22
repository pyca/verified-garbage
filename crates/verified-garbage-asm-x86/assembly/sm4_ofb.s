// The functions of `src/sm4_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ofb_aesni:
	lea esp, [esp-688]
	mov eax, DWORD PTR [esp+692]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+696]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+700]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+704]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+624], ebx
	mov DWORD PTR [eax+628], esi
	mov DWORD PTR [eax+632], edi
	mov DWORD PTR [eax+636], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+660], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
	movdqu xmm7, XMMWORD PTR [ebx]
20:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ebx+224]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [esi], xmm3
	pshufd xmm3, xmm2, 85
	movdqu XMMWORD PTR [esi+16], xmm3
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [esi+32], xmm3
	pshufd xmm3, xmm2, 255
	movdqu XMMWORD PTR [esi+48], xmm3
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+644], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+640]
	mov ebp, DWORD PTR [edi+644]
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm0, XMMWORD PTR [edi+8]
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [edi+32], xmm3
	pshufd xmm0, xmm2, 85
	movdqu XMMWORD PTR [edi+48], xmm0
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [edi+64], xmm3
	pshufd xmm1, xmm2, 255
	movdqu XMMWORD PTR [edi+80], xmm1
	pxor xmm0, xmm3
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm0, xmm3
24:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm1
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu xmm2, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm2
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm1
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqu xmm0, XMMWORD PTR [edi+80]
	movdqu xmm1, XMMWORD PTR [edi+64]
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 136
	movdqu xmm1, XMMWORD PTR [edi+48]
	movdqu xmm2, XMMWORD PTR [edi+32]
	punpcklqdq xmm1, xmm2
	pshufd xmm1, xmm1, 136
	punpcklqdq xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+8], xmm2
	mov esi, DWORD PTR [edi+640]
	mov ebp, DWORD PTR [edi+644]
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+640], esi
	mov DWORD PTR [edi+644], ebp
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+624]
	mov esi, DWORD PTR [edi+628]
	mov ebp, DWORD PTR [edi+636]
	mov edi, DWORD PTR [edi+632]
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
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	lea esp, [esp+688]
	lea esp, [esp-692]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+692]
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

vg_sm4_ofb:
	lea esp, [esp-1496]
	mov eax, DWORD PTR [esp+1500]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1504]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1508]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1512]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1432], ebx
	mov DWORD PTR [eax+1436], esi
	mov DWORD PTR [eax+1440], edi
	mov DWORD PTR [eax+1444], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1468], eax
	mov eax, 179
	mov edx, 0
	mov ecx, DWORD PTR [esp+4]
	push eax
	push edi
	push edx
	push ecx
	call {vg_sm4_prepare_keys}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1452], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+268], eax
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, 179
	push eax
	push edi
	call {vg_sm4_crypt_prepared}
	pop eax
	pop eax
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1432]
	mov esi, DWORD PTR [edi+1436]
	mov ebp, DWORD PTR [edi+1444]
	mov edi, DWORD PTR [edi+1440]
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
	lea esp, [esp+1496]
	lea esp, [esp-1516]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	lea esp, [esp+1516]
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

vg_sm4_ofb_final_aesni:
	lea esp, [esp-688]
	mov eax, DWORD PTR [esp+692]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+696]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+700]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+704]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+624], ebx
	mov DWORD PTR [eax+628], esi
	mov DWORD PTR [eax+632], edi
	mov DWORD PTR [eax+636], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+660], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
	movdqu xmm7, XMMWORD PTR [ebx]
20:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ebx+224]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [esi], xmm3
	pshufd xmm3, xmm2, 85
	movdqu XMMWORD PTR [esi+16], xmm3
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [esi+32], xmm3
	pshufd xmm3, xmm2, 255
	movdqu XMMWORD PTR [esi+48], xmm3
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+644], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+640]
	mov ebp, DWORD PTR [edi+644]
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm0, XMMWORD PTR [edi+8]
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [edi+32], xmm3
	pshufd xmm0, xmm2, 85
	movdqu XMMWORD PTR [edi+48], xmm0
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [edi+64], xmm3
	pshufd xmm1, xmm2, 255
	movdqu XMMWORD PTR [edi+80], xmm1
	pxor xmm0, xmm3
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm0, xmm3
24:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm1
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu xmm2, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm2
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm1
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqu xmm0, XMMWORD PTR [edi+80]
	movdqu xmm1, XMMWORD PTR [edi+64]
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 136
	movdqu xmm1, XMMWORD PTR [edi+48]
	movdqu xmm2, XMMWORD PTR [edi+32]
	punpcklqdq xmm1, xmm2
	pshufd xmm1, xmm1, 136
	punpcklqdq xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+8], xmm2
	mov esi, DWORD PTR [edi+640]
	mov ebp, DWORD PTR [edi+644]
	cmp ebp, 16
	jb 25f
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+640], esi
	mov DWORD PTR [edi+644], ebp
	jmp 26f
25:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+660], eax
	mov ebx, edi
	add ebx, 8
27:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 27b
	mov DWORD PTR [edi+640], esi
	mov DWORD PTR [edi+644], ebp
26:
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+624]
	mov esi, DWORD PTR [edi+628]
	mov ebp, DWORD PTR [edi+636]
	mov edi, DWORD PTR [edi+632]
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
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	lea esp, [esp+688]
	lea esp, [esp-692]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+692]
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

vg_sm4_ofb_final:
	lea esp, [esp-1496]
	mov eax, DWORD PTR [esp+1500]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1504]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1508]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1512]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1432], ebx
	mov DWORD PTR [eax+1436], esi
	mov DWORD PTR [eax+1440], edi
	mov DWORD PTR [eax+1444], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1468], eax
	mov eax, 179
	mov edx, 0
	mov ecx, DWORD PTR [esp+4]
	push eax
	push edi
	push edx
	push ecx
	call {vg_sm4_prepare_keys}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1452], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+268], eax
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov eax, 179
	push eax
	push edi
	call {vg_sm4_crypt_prepared}
	pop eax
	pop eax
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	cmp ebp, 16
	jb 23f
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+264]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+268]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	jmp 24f
23:
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+1468], eax
	mov ebx, edi
	add ebx, 256
25:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 25b
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
24:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1432]
	mov esi, DWORD PTR [edi+1436]
	mov ebp, DWORD PTR [edi+1444]
	mov edi, DWORD PTR [edi+1440]
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
	lea esp, [esp+1496]
	lea esp, [esp-1516]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	lea esp, [esp+1516]
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
