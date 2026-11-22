// The functions of `src/seed_cbc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cbc_encrypt_chained_aesni:
	lea esp, [esp-672]
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+608], ebx
	mov DWORD PTR [eax+612], esi
	mov DWORD PTR [eax+616], edi
	mov DWORD PTR [eax+620], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+644], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+628], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+624]
	mov ebp, DWORD PTR [edi+628]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm0, XMMWORD PTR [edi+8]
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [edi+32], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [edi+48], xmm1
	pshufd xmm5, xmm0, 170
	pshufd xmm0, xmm0, 255
24:
	movdqu XMMWORD PTR [edi+64], xmm5
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm6, xmm0
	paddd xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	paddd xmm0, xmm6
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm6, xmm0
	paddd xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	paddd xmm0, xmm6
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	punpcklqdq xmm5, xmm0
	pshufd xmm5, xmm5, 136
	movdqu xmm1, XMMWORD PTR [edi+32]
	movdqu xmm2, XMMWORD PTR [edi+48]
	punpcklqdq xmm1, xmm2
	pshufd xmm1, xmm1, 136
	punpcklqdq xmm5, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm5, xmm4
	movdqu XMMWORD PTR [edi+8], xmm5
	mov esi, DWORD PTR [edi+624]
	mov ebp, DWORD PTR [edi+628]
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+624], esi
	mov DWORD PTR [edi+628], ebp
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+608]
	mov esi, DWORD PTR [edi+612]
	mov ebp, DWORD PTR [edi+620]
	mov edi, DWORD PTR [edi+616]
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	lea esp, [esp+672]
	lea esp, [esp-676]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+676]
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

vg_seed_cbc_encrypt_chained:
	lea esp, [esp-1168]
	mov eax, DWORD PTR [esp+1172]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1184]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1104], ebx
	mov DWORD PTR [eax+1108], esi
	mov DWORD PTR [eax+1112], edi
	mov DWORD PTR [eax+1116], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1124], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+988], eax
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esp+4]
	mov ecx, edi
	add ecx, 976
	mov edx, 8
	push edi
	push edx
	push ecx
	push eax
	call {vg_seed_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1104]
	mov esi, DWORD PTR [edi+1108]
	mov ebp, DWORD PTR [edi+1116]
	mov edi, DWORD PTR [edi+1112]
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	mov DWORD PTR [esp+1108], ecx
	mov DWORD PTR [esp+1112], ecx
	mov DWORD PTR [esp+1116], ecx
	mov DWORD PTR [esp+1120], ecx
	mov DWORD PTR [esp+1124], ecx
	mov DWORD PTR [esp+1128], ecx
	mov DWORD PTR [esp+1132], ecx
	mov DWORD PTR [esp+1136], ecx
	mov DWORD PTR [esp+1140], ecx
	mov DWORD PTR [esp+1144], ecx
	mov DWORD PTR [esp+1148], ecx
	mov DWORD PTR [esp+1152], ecx
	mov DWORD PTR [esp+1156], ecx
	mov DWORD PTR [esp+1160], ecx
	mov DWORD PTR [esp+1164], ecx
	lea esp, [esp+1168]
	lea esp, [esp-1188]
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
	lea esp, [esp+1188]
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

vg_seed_cbc_decrypt_chained:
	lea esp, [esp-1168]
	mov eax, DWORD PTR [esp+1172]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1184]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1104], ebx
	mov DWORD PTR [eax+1108], esi
	mov DWORD PTR [eax+1112], edi
	mov DWORD PTR [eax+1116], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1124], eax
	test eax, eax
	mov eax, DWORD PTR [edi+1124]
	cmp eax, 8
	jb 20f
22:
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1100], eax
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esp+4]
	mov ecx, edi
	add ecx, 976
	mov edx, 8
	push edi
	push edx
	push ecx
	push eax
	call {vg_seed_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [edi+976]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+984]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+988]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+992]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1008]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1012]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1016]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1020]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1040]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1056]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1060]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1064]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1068]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1072]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1088]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	cmp ebp, 8
	jae 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [edi+1124]
	cmp eax, 4
	jb 23f
25:
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1036], eax
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esp+4]
	mov ecx, edi
	add ecx, 976
	mov edx, 8
	push edi
	push edx
	push ecx
	push eax
	call {vg_seed_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [edi+976]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+984]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+988]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+992]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1008]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1012]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1016]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1020]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	cmp ebp, 4
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+1124]
	cmp eax, 2
	jb 26f
28:
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1004], eax
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esp+4]
	mov ecx, edi
	add ecx, 976
	mov edx, 8
	push edi
	push edx
	push ecx
	push eax
	call {vg_seed_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [edi+976]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+984]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+988]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+992]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+996]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1000]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1004]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	cmp ebp, 2
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+1124]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+988], eax
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [esp+4]
	mov ecx, edi
	add ecx, 976
	mov edx, 8
	push edi
	push edx
	push ecx
	push eax
	call {vg_seed_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	mov esi, DWORD PTR [edi+1120]
	mov ebp, DWORD PTR [edi+1124]
	mov eax, DWORD PTR [edi+976]
	xor eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+980]
	xor eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+984]
	xor eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+988]
	xor eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1120], esi
	mov DWORD PTR [edi+1124], ebp
	jne 211b
	jmp 210f
29:
210:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1104]
	mov esi, DWORD PTR [edi+1108]
	mov ebp, DWORD PTR [edi+1116]
	mov edi, DWORD PTR [edi+1112]
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	mov DWORD PTR [esp+752], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	mov DWORD PTR [esp+768], ecx
	mov DWORD PTR [esp+772], ecx
	mov DWORD PTR [esp+776], ecx
	mov DWORD PTR [esp+780], ecx
	mov DWORD PTR [esp+784], ecx
	mov DWORD PTR [esp+788], ecx
	mov DWORD PTR [esp+792], ecx
	mov DWORD PTR [esp+796], ecx
	mov DWORD PTR [esp+800], ecx
	mov DWORD PTR [esp+804], ecx
	mov DWORD PTR [esp+808], ecx
	mov DWORD PTR [esp+812], ecx
	mov DWORD PTR [esp+816], ecx
	mov DWORD PTR [esp+820], ecx
	mov DWORD PTR [esp+824], ecx
	mov DWORD PTR [esp+828], ecx
	mov DWORD PTR [esp+832], ecx
	mov DWORD PTR [esp+836], ecx
	mov DWORD PTR [esp+840], ecx
	mov DWORD PTR [esp+844], ecx
	mov DWORD PTR [esp+848], ecx
	mov DWORD PTR [esp+852], ecx
	mov DWORD PTR [esp+856], ecx
	mov DWORD PTR [esp+860], ecx
	mov DWORD PTR [esp+864], ecx
	mov DWORD PTR [esp+868], ecx
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	mov DWORD PTR [esp+884], ecx
	mov DWORD PTR [esp+888], ecx
	mov DWORD PTR [esp+892], ecx
	mov DWORD PTR [esp+896], ecx
	mov DWORD PTR [esp+900], ecx
	mov DWORD PTR [esp+904], ecx
	mov DWORD PTR [esp+908], ecx
	mov DWORD PTR [esp+912], ecx
	mov DWORD PTR [esp+916], ecx
	mov DWORD PTR [esp+920], ecx
	mov DWORD PTR [esp+924], ecx
	mov DWORD PTR [esp+928], ecx
	mov DWORD PTR [esp+932], ecx
	mov DWORD PTR [esp+936], ecx
	mov DWORD PTR [esp+940], ecx
	mov DWORD PTR [esp+944], ecx
	mov DWORD PTR [esp+948], ecx
	mov DWORD PTR [esp+952], ecx
	mov DWORD PTR [esp+956], ecx
	mov DWORD PTR [esp+960], ecx
	mov DWORD PTR [esp+964], ecx
	mov DWORD PTR [esp+968], ecx
	mov DWORD PTR [esp+972], ecx
	mov DWORD PTR [esp+976], ecx
	mov DWORD PTR [esp+980], ecx
	mov DWORD PTR [esp+984], ecx
	mov DWORD PTR [esp+988], ecx
	mov DWORD PTR [esp+992], ecx
	mov DWORD PTR [esp+996], ecx
	mov DWORD PTR [esp+1000], ecx
	mov DWORD PTR [esp+1004], ecx
	mov DWORD PTR [esp+1008], ecx
	mov DWORD PTR [esp+1012], ecx
	mov DWORD PTR [esp+1016], ecx
	mov DWORD PTR [esp+1020], ecx
	mov DWORD PTR [esp+1024], ecx
	mov DWORD PTR [esp+1028], ecx
	mov DWORD PTR [esp+1032], ecx
	mov DWORD PTR [esp+1036], ecx
	mov DWORD PTR [esp+1040], ecx
	mov DWORD PTR [esp+1044], ecx
	mov DWORD PTR [esp+1048], ecx
	mov DWORD PTR [esp+1052], ecx
	mov DWORD PTR [esp+1056], ecx
	mov DWORD PTR [esp+1060], ecx
	mov DWORD PTR [esp+1064], ecx
	mov DWORD PTR [esp+1068], ecx
	mov DWORD PTR [esp+1072], ecx
	mov DWORD PTR [esp+1076], ecx
	mov DWORD PTR [esp+1080], ecx
	mov DWORD PTR [esp+1084], ecx
	mov DWORD PTR [esp+1088], ecx
	mov DWORD PTR [esp+1092], ecx
	mov DWORD PTR [esp+1096], ecx
	mov DWORD PTR [esp+1100], ecx
	mov DWORD PTR [esp+1104], ecx
	mov DWORD PTR [esp+1108], ecx
	mov DWORD PTR [esp+1112], ecx
	mov DWORD PTR [esp+1116], ecx
	mov DWORD PTR [esp+1120], ecx
	mov DWORD PTR [esp+1124], ecx
	mov DWORD PTR [esp+1128], ecx
	mov DWORD PTR [esp+1132], ecx
	mov DWORD PTR [esp+1136], ecx
	mov DWORD PTR [esp+1140], ecx
	mov DWORD PTR [esp+1144], ecx
	mov DWORD PTR [esp+1148], ecx
	mov DWORD PTR [esp+1152], ecx
	mov DWORD PTR [esp+1156], ecx
	mov DWORD PTR [esp+1160], ecx
	mov DWORD PTR [esp+1164], ecx
	lea esp, [esp+1168]
	lea esp, [esp-1188]
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
	lea esp, [esp+1188]
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
