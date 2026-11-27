// The functions of `src/sm4.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key_aesni:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_KEY_AESNI}
	pop ecx
	mov edx, DWORD PTR [esp+8]
	movdqu xmm6, XMMWORD PTR [eax+256]
	movdqu XMMWORD PTR [edx], xmm6
	movdqu xmm6, XMMWORD PTR [eax+272]
	movdqu XMMWORD PTR [edx+16], xmm6
	movdqu xmm6, XMMWORD PTR [eax+288]
	movdqu XMMWORD PTR [edx+32], xmm6
	movdqu xmm6, XMMWORD PTR [eax+304]
	movdqu XMMWORD PTR [edx+48], xmm6
	movdqu xmm6, XMMWORD PTR [eax+320]
	movdqu XMMWORD PTR [edx+64], xmm6
	movdqu xmm6, XMMWORD PTR [eax+336]
	movdqu XMMWORD PTR [edx+80], xmm6
	movdqu xmm6, XMMWORD PTR [eax+352]
	movdqu XMMWORD PTR [edx+96], xmm6
	movdqu xmm6, XMMWORD PTR [eax+368]
	movdqu XMMWORD PTR [edx+112], xmm6
	mov ecx, DWORD PTR [esp+4]
	movdqu xmm7, XMMWORD PTR [eax]
	movdqu xmm4, XMMWORD PTR [ecx]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+16]
	pshufb xmm6, xmm4
	movdqu xmm4, XMMWORD PTR [eax+32]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [eax+224]
	pxor xmm6, xmm5
	pshufd xmm0, xmm6, 0
	pshufd xmm1, xmm6, 85
	pshufd xmm2, xmm6, 170
	pshufd xmm3, xmm6, 255
	mov ecx, 8
20:
	movdqu xmm4, XMMWORD PTR [edx]
	pxor xmm4, xmm1
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 1
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	pxor xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 2
	pxor xmm4, xmm3
	pxor xmm4, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 3
	pxor xmm4, xmm0
	pxor xmm4, xmm1
	pxor xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm6, xmm0
	punpcklqdq xmm6, xmm1
	pshufd xmm6, xmm6, 136
	movdqa xmm5, xmm2
	punpcklqdq xmm5, xmm3
	pshufd xmm5, xmm5, 136
	punpcklqdq xmm6, xmm5
	movdqa xmm5, xmm6
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [eax+48]
	pshufb xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	pshufb xmm6, xmm5
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	pshufb xmm4, xmm6
	movdqu XMMWORD PTR [edx], xmm4
	add edx, 16
	sub ecx, 1
	jne 20b
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

vg_sm4_expand_key:
	lea esp, [esp-1444]
	mov eax, DWORD PTR [esp+1448]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+1452]
	mov DWORD PTR [esp+4], eax
	mov eax, esp
	add eax, 12
	mov DWORD PTR [esp+8], eax
	call {vg_sm4_expand_key_shared}
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+12], xmm0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	mov DWORD PTR [esp+1436], ecx
	mov DWORD PTR [esp+1440], ecx
	lea esp, [esp+1444]
	lea esp, [esp-1448]
	movdqu XMMWORD PTR [esp], xmm0
	lea esp, [esp+1448]
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

vg_sm4_ecb_encrypt_aesni:
	lea esp, [esp-752]
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+688], ebx
	mov DWORD PTR [eax+692], esi
	mov DWORD PTR [eax+696], edi
	mov DWORD PTR [eax+700], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_AESNI_WIDE}
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
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+708]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+684], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
24:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+708]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+652], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
28:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	jne 28b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+708]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
212:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	jne 212b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+688]
	mov esi, DWORD PTR [edi+692]
	mov ebp, DWORD PTR [edi+700]
	mov edi, DWORD PTR [edi+696]
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
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	lea esp, [esp+752]
	lea esp, [esp-756]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+752], ecx
	lea esp, [esp+756]
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

vg_sm4_ecb_encrypt:
	lea esp, [esp-1492]
	mov eax, DWORD PTR [esp+1496]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1500]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1504]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+1432], ebx
	mov DWORD PTR [eax+1436], esi
	mov DWORD PTR [eax+1440], edi
	mov DWORD PTR [eax+1444], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 384
	mov ebp, 32
20:
	mov eax, DWORD PTR [ecx]
	bswap eax
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	add ecx, 4
	add esi, 32
	sub ebp, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1452], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov ecx, ebp
	cmp ebp, 8
	jb 24f
	mov ecx, 8
	jmp 25f
24:
25:
	mov edx, esi
	mov ebx, edi
	add ebx, 256
26:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 26b
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
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
	mov ecx, ebp
	cmp ebp, 8
	jb 27f
	mov ecx, 8
	jmp 28f
27:
28:
	mov edx, edi
	add edx, 256
	mov ebx, esi
29:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 29b
	mov ecx, ebp
	cmp ebp, 8
	jb 210f
	mov ecx, 8
	jmp 211f
210:
211:
	add esi, 128
	sub ebp, ecx
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	jne 23b
	jmp 22f
21:
22:
	mov ebx, DWORD PTR [edi+1432]
	mov esi, DWORD PTR [edi+1436]
	mov ebp, DWORD PTR [edi+1444]
	mov edi, DWORD PTR [edi+1440]
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
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	movdqu XMMWORD PTR [esp+1108], xmm0
	movdqu XMMWORD PTR [esp+1124], xmm0
	movdqu XMMWORD PTR [esp+1140], xmm0
	movdqu XMMWORD PTR [esp+1156], xmm0
	movdqu XMMWORD PTR [esp+1172], xmm0
	movdqu XMMWORD PTR [esp+1188], xmm0
	movdqu XMMWORD PTR [esp+1204], xmm0
	movdqu XMMWORD PTR [esp+1220], xmm0
	movdqu XMMWORD PTR [esp+1236], xmm0
	movdqu XMMWORD PTR [esp+1252], xmm0
	movdqu XMMWORD PTR [esp+1268], xmm0
	movdqu XMMWORD PTR [esp+1284], xmm0
	movdqu XMMWORD PTR [esp+1300], xmm0
	movdqu XMMWORD PTR [esp+1316], xmm0
	movdqu XMMWORD PTR [esp+1332], xmm0
	movdqu XMMWORD PTR [esp+1348], xmm0
	movdqu XMMWORD PTR [esp+1364], xmm0
	movdqu XMMWORD PTR [esp+1380], xmm0
	movdqu XMMWORD PTR [esp+1396], xmm0
	movdqu XMMWORD PTR [esp+1412], xmm0
	movdqu XMMWORD PTR [esp+1428], xmm0
	movdqu XMMWORD PTR [esp+1444], xmm0
	movdqu XMMWORD PTR [esp+1460], xmm0
	movdqu XMMWORD PTR [esp+1476], xmm0
	lea esp, [esp+1492]
	lea esp, [esp-1512]
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
	lea esp, [esp+1512]
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

vg_sm4_ecb_decrypt_aesni:
	lea esp, [esp-752]
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+688], ebx
	mov DWORD PTR [eax+692], esi
	mov DWORD PTR [eax+696], edi
	mov DWORD PTR [eax+700], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 544
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
	pshufd xmm3, xmm2, 255
	movdqu XMMWORD PTR [esi], xmm3
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [esi+16], xmm3
	pshufd xmm3, xmm2, 85
	movdqu XMMWORD PTR [esi+32], xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [esi+48], xmm3
	add eax, 16
	sub esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+708]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+684], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
24:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+708]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+652], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
28:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	jne 28b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+708]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
212:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
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
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
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
	jne 212b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+688]
	mov esi, DWORD PTR [edi+692]
	mov ebp, DWORD PTR [edi+700]
	mov edi, DWORD PTR [edi+696]
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
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	lea esp, [esp+752]
	lea esp, [esp-756]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+752], ecx
	lea esp, [esp+756]
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

vg_sm4_ecb_decrypt:
	lea esp, [esp-1492]
	mov eax, DWORD PTR [esp+1496]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1500]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1504]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+1432], ebx
	mov DWORD PTR [eax+1436], esi
	mov DWORD PTR [eax+1440], edi
	mov DWORD PTR [eax+1444], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 1376
	mov ebp, 32
20:
	mov eax, DWORD PTR [ecx]
	bswap eax
	mov DWORD PTR [edi], eax
	mov ebx, DWORD PTR [edi]
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 1
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 2
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 3
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 4
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 5
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 6
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [edi]
	shr ebx, 7
	and ebx, 16843009
	mov edx, ebx
	ror edx, 31
	xor ebx, edx
	mov edx, ebx
	ror edx, 30
	xor ebx, edx
	mov edx, ebx
	ror edx, 28
	xor ebx, edx
	mov DWORD PTR [esi+28], ebx
	add ecx, 4
	sub esi, 32
	sub ebp, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+1448], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1452], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+1448]
	mov ebp, DWORD PTR [edi+1452]
	mov ecx, ebp
	cmp ebp, 8
	jb 24f
	mov ecx, 8
	jmp 25f
24:
25:
	mov edx, esi
	mov ebx, edi
	add ebx, 256
26:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 26b
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
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
	mov ecx, ebp
	cmp ebp, 8
	jb 27f
	mov ecx, 8
	jmp 28f
27:
28:
	mov edx, edi
	add edx, 256
	mov ebx, esi
29:
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+12], eax
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 29b
	mov ecx, ebp
	cmp ebp, 8
	jb 210f
	mov ecx, 8
	jmp 211f
210:
211:
	add esi, 128
	sub ebp, ecx
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	jne 23b
	jmp 22f
21:
22:
	mov ebx, DWORD PTR [edi+1432]
	mov esi, DWORD PTR [edi+1436]
	mov ebp, DWORD PTR [edi+1444]
	mov edi, DWORD PTR [edi+1440]
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
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	movdqu XMMWORD PTR [esp+1108], xmm0
	movdqu XMMWORD PTR [esp+1124], xmm0
	movdqu XMMWORD PTR [esp+1140], xmm0
	movdqu XMMWORD PTR [esp+1156], xmm0
	movdqu XMMWORD PTR [esp+1172], xmm0
	movdqu XMMWORD PTR [esp+1188], xmm0
	movdqu XMMWORD PTR [esp+1204], xmm0
	movdqu XMMWORD PTR [esp+1220], xmm0
	movdqu XMMWORD PTR [esp+1236], xmm0
	movdqu XMMWORD PTR [esp+1252], xmm0
	movdqu XMMWORD PTR [esp+1268], xmm0
	movdqu XMMWORD PTR [esp+1284], xmm0
	movdqu XMMWORD PTR [esp+1300], xmm0
	movdqu XMMWORD PTR [esp+1316], xmm0
	movdqu XMMWORD PTR [esp+1332], xmm0
	movdqu XMMWORD PTR [esp+1348], xmm0
	movdqu XMMWORD PTR [esp+1364], xmm0
	movdqu XMMWORD PTR [esp+1380], xmm0
	movdqu XMMWORD PTR [esp+1396], xmm0
	movdqu XMMWORD PTR [esp+1412], xmm0
	movdqu XMMWORD PTR [esp+1428], xmm0
	movdqu XMMWORD PTR [esp+1444], xmm0
	movdqu XMMWORD PTR [esp+1460], xmm0
	movdqu XMMWORD PTR [esp+1476], xmm0
	lea esp, [esp+1492]
	lea esp, [esp-1512]
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
	lea esp, [esp+1512]
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
