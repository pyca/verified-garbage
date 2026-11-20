// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_random:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-1088]
	mov edx, DWORD PTR [esp+1124]
	mov eax, DWORD PTR [esp+1140]
	sub edx, eax
	sub edx, 3
	mov esi, DWORD PTR [esp+1144]
	mov ecx, DWORD PTR [esp+1148]
	mov edi, esp
	add edi, 64
	cmp ecx, 0
	jne 20f
	jmp 21f
20:
22:
	movzx eax, BYTE PTR [esi]
	add esi, 1
	sub ecx, 1
	test eax, eax
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [edi], al
	add edi, 1
	sub edx, 1
24:
	cmp edx, 0
	je 25f
	test ecx, ecx
	jmp 26f
25:
26:
	jne 22b
21:
	cmp edx, 0
	je 27f
	mov esi, DWORD PTR [esp+1108]
	mov ecx, DWORD PTR [esp+1124]
	mov eax, 0
29:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 29b
	mov ecx, DWORD PTR [esp+1124]
	mov eax, DWORD PTR [esp+1140]
	sub ecx, eax
	sub ecx, 3
	sub ecx, edx
	mov esi, esp
	add esi, 64
	mov eax, 0
	test ecx, ecx
	jne 210f
	jmp 211f
210:
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
211:
	mov eax, DWORD PTR [esp+1148]
	mov ebx, DWORD PTR [esp+1124]
	mov ecx, DWORD PTR [esp+1140]
	sub ebx, ecx
	add ebx, 125
	mov esi, DWORD PTR [esp+1116]
	cmp eax, ebx
	jae 213f
	add eax, edx
	cmp ebx, eax
	jb 215f
	jmp 216f
215:
	mov eax, ebx
216:
	mov ebx, 0
	mov DWORD PTR [esi], ebx
	mov DWORD PTR [esi+4], ebx
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], ebx
	mov eax, 0
	jmp 214f
213:
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov DWORD PTR [esi+8], eax
	mov DWORD PTR [esi+12], eax
	mov eax, 3
214:
	jmp 28f
27:
	mov eax, DWORD PTR [esp+1116]
	mov ebx, DWORD PTR [esp+1148]
	sub ebx, ecx
	mov DWORD PTR [eax], ebx
	mov ebx, 0
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], ebx
	mov DWORD PTR [eax+12], ebx
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+1124]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1128]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1132]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1136]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1140]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 64
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+1124]
	mov ebx, DWORD PTR [esp+1140]
	sub eax, ebx
	sub eax, 3
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+1152]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+1156]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+1160]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+1164]
	mov DWORD PTR [esp+52], eax
	call {vg_rsa_pkcs1_encrypt_precomputed}
	mov ebx, 2
	sub ebx, eax
	mov esi, esp
	add esi, 64
	mov ecx, DWORD PTR [esp+1124]
	mov eax, DWORD PTR [esp+1140]
	sub ecx, eax
	sub ecx, 3
	mov eax, 0
217:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 217b
	mov eax, ebx
28:
	lea esp, [esp+1088]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2296]
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
	mov DWORD PTR [esp+2288], ecx
	mov DWORD PTR [esp+2292], ecx
	lea esp, [esp+2296]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-104]
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+84], eax
	call {vg_rsa_private_checked_precomputed}
	mov DWORD PTR [esp+80], eax
	mov esi, DWORD PTR [esp+208]
	add esi, 1552
	mov ecx, DWORD PTR [esp+140]
	mov eax, 0
20:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 20b
	mov ebx, DWORD PTR [esp+208]
	add ebx, 1552
	add ebx, DWORD PTR [esp+140]
	sub ebx, DWORD PTR [esp+156]
	mov esi, DWORD PTR [esp+152]
	mov ecx, DWORD PTR [esp+156]
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	push edi
	call {vg_sha256_init_core}
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 1552
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov eax, DWORD PTR [esp+140]
	mov ecx, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+160]
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, DWORD PTR [esp+140]
	add eax, 64
	mov ecx, 0
	mov edi, DWORD PTR [esp+208]
	add edi, 240
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 8
	mov DWORD PTR [esp+88], eax
22:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 108
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 110
	mov BYTE PTR [ebx+4], al
	mov eax, 103
	mov BYTE PTR [ebx+5], al
	mov eax, 116
	mov BYTE PTR [ebx+6], al
	mov eax, 104
	mov BYTE PTR [ebx+7], al
	mov eax, 8
	mov BYTE PTR [ebx+8], al
	mov eax, 0
	mov BYTE PTR [ebx+9], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 10
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 74
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 272
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 22b
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+140]
	add eax, 31
	shr eax, 5
	mov DWORD PTR [esp+88], eax
23:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 109
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 115
	mov BYTE PTR [ebx+4], al
	mov eax, 115
	mov BYTE PTR [ebx+5], al
	mov eax, 97
	mov BYTE PTR [ebx+6], al
	mov eax, 103
	mov BYTE PTR [ebx+7], al
	mov eax, 101
	mov BYTE PTR [ebx+8], al
	mov eax, edx
	shr eax, 5
	mov BYTE PTR [ebx+9], al
	mov eax, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov BYTE PTR [ebx+10], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 11
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 75
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 528
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 23b
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 11
	mov eax, 0
24:
	add eax, eax
	add eax, 1
	cmp eax, ecx
	jb 24b
	mov esi, DWORD PTR [esp+208]
	add esi, 272
	mov edi, eax
	mov ebp, ecx
	mov ebx, 0
	mov ecx, 128
25:
	movzx eax, BYTE PTR [esi]
	ror eax, 24
	movzx edx, BYTE PTR [esi+1]
	or eax, edx
	and eax, edi
	mov edx, ebp
	sub edx, eax
	sbb edx, edx
	xor edx, -1
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	add esi, 2
	sub ecx, 1
	jne 25b
	mov DWORD PTR [esp+92], ebx
	mov esi, DWORD PTR [esp+124]
	add esi, 2
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 2
	mov edx, 2
	mov ebx, 0
	mov edi, 0
26:
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	mov ebp, ebx
	xor ebp, -1
	and ebp, eax
	and ebp, edx
	or edi, ebp
	or ebx, eax
	add edx, 1
	add esi, 1
	sub ecx, 1
	jne 26b
	mov esi, DWORD PTR [esp+124]
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	movzx edx, BYTE PTR [esi+1]
	xor edx, 2
	sub edx, 1
	sbb edx, edx
	and eax, edx
	and eax, ebx
	mov edx, edi
	sub edx, 10
	sbb edx, edx
	xor edx, -1
	and eax, edx
	mov DWORD PTR [esp+96], eax
	mov edx, DWORD PTR [esp+140]
	sub edx, edi
	sub edx, 1
	mov ecx, DWORD PTR [esp+92]
	xor edx, ecx
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [esp+80]
	xor eax, 1
	sub eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov ebx, DWORD PTR [esp+140]
	sub ebx, edx
	and edx, eax
	mov esi, DWORD PTR [esp+132]
	mov DWORD PTR [esi], edx
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov esi, DWORD PTR [esp+124]
	mov edi, DWORD PTR [esp+208]
	add edi, 528
	mov edx, 0
	mov ecx, DWORD PTR [esp+140]
27:
	movzx eax, BYTE PTR [esi]
	movzx ebp, BYTE PTR [edi]
	xor eax, ebp
	and eax, DWORD PTR [esp+96]
	xor eax, ebp
	mov ebp, edx
	sub ebp, ebx
	sbb ebp, ebp
	xor ebp, -1
	and ebp, DWORD PTR [esp+100]
	and eax, ebp
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	mov eax, DWORD PTR [esp+80]
	lea esp, [esp+104]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	lea esp, [esp-3568]
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
	movdqu XMMWORD PTR [esp+3520], xmm0
	movdqu XMMWORD PTR [esp+3536], xmm0
	movdqu XMMWORD PTR [esp+3552], xmm0
	lea esp, [esp+3568]
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

vg_rsa_pkcs1_decrypt_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-104]
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+84], eax
	call {vg_rsa_private_checked_precomputed}
	mov DWORD PTR [esp+80], eax
	mov esi, DWORD PTR [esp+208]
	add esi, 1552
	mov ecx, DWORD PTR [esp+140]
	mov eax, 0
20:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 20b
	mov ebx, DWORD PTR [esp+208]
	add ebx, 1552
	add ebx, DWORD PTR [esp+140]
	sub ebx, DWORD PTR [esp+156]
	mov esi, DWORD PTR [esp+152]
	mov ecx, DWORD PTR [esp+156]
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	push edi
	call {vg_sha256_init_core}
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 1552
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov eax, DWORD PTR [esp+140]
	mov ecx, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+160]
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, DWORD PTR [esp+140]
	add eax, 64
	mov ecx, 0
	mov edi, DWORD PTR [esp+208]
	add edi, 240
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 8
	mov DWORD PTR [esp+88], eax
22:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 108
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 110
	mov BYTE PTR [ebx+4], al
	mov eax, 103
	mov BYTE PTR [ebx+5], al
	mov eax, 116
	mov BYTE PTR [ebx+6], al
	mov eax, 104
	mov BYTE PTR [ebx+7], al
	mov eax, 8
	mov BYTE PTR [ebx+8], al
	mov eax, 0
	mov BYTE PTR [ebx+9], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 10
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 74
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 272
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 22b
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+140]
	add eax, 31
	shr eax, 5
	mov DWORD PTR [esp+88], eax
23:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 109
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 115
	mov BYTE PTR [ebx+4], al
	mov eax, 115
	mov BYTE PTR [ebx+5], al
	mov eax, 97
	mov BYTE PTR [ebx+6], al
	mov eax, 103
	mov BYTE PTR [ebx+7], al
	mov eax, 101
	mov BYTE PTR [ebx+8], al
	mov eax, edx
	shr eax, 5
	mov BYTE PTR [ebx+9], al
	mov eax, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov BYTE PTR [ebx+10], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 11
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 75
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 528
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 23b
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 11
	mov eax, 0
24:
	add eax, eax
	add eax, 1
	cmp eax, ecx
	jb 24b
	mov esi, DWORD PTR [esp+208]
	add esi, 272
	mov edi, eax
	mov ebp, ecx
	mov ebx, 0
	mov ecx, 128
25:
	movzx eax, BYTE PTR [esi]
	ror eax, 24
	movzx edx, BYTE PTR [esi+1]
	or eax, edx
	and eax, edi
	mov edx, ebp
	sub edx, eax
	sbb edx, edx
	xor edx, -1
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	add esi, 2
	sub ecx, 1
	jne 25b
	mov DWORD PTR [esp+92], ebx
	mov esi, DWORD PTR [esp+124]
	add esi, 2
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 2
	mov edx, 2
	mov ebx, 0
	mov edi, 0
26:
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	mov ebp, ebx
	xor ebp, -1
	and ebp, eax
	and ebp, edx
	or edi, ebp
	or ebx, eax
	add edx, 1
	add esi, 1
	sub ecx, 1
	jne 26b
	mov esi, DWORD PTR [esp+124]
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	movzx edx, BYTE PTR [esi+1]
	xor edx, 2
	sub edx, 1
	sbb edx, edx
	and eax, edx
	and eax, ebx
	mov edx, edi
	sub edx, 10
	sbb edx, edx
	xor edx, -1
	and eax, edx
	mov DWORD PTR [esp+96], eax
	mov edx, DWORD PTR [esp+140]
	sub edx, edi
	sub edx, 1
	mov ecx, DWORD PTR [esp+92]
	xor edx, ecx
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [esp+80]
	xor eax, 1
	sub eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov ebx, DWORD PTR [esp+140]
	sub ebx, edx
	and edx, eax
	mov esi, DWORD PTR [esp+132]
	mov DWORD PTR [esi], edx
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov esi, DWORD PTR [esp+124]
	mov edi, DWORD PTR [esp+208]
	add edi, 528
	mov edx, 0
	mov ecx, DWORD PTR [esp+140]
27:
	movzx eax, BYTE PTR [esi]
	movzx ebp, BYTE PTR [edi]
	xor eax, ebp
	and eax, DWORD PTR [esp+96]
	xor eax, ebp
	mov ebp, edx
	sub ebp, ebx
	sbb ebp, ebp
	xor ebp, -1
	and ebp, DWORD PTR [esp+100]
	and eax, ebp
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	mov eax, DWORD PTR [esp+80]
	lea esp, [esp+104]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	pxor xmm0, xmm0
	lea esp, [esp-3568]
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
	movdqu XMMWORD PTR [esp+3520], xmm0
	movdqu XMMWORD PTR [esp+3536], xmm0
	movdqu XMMWORD PTR [esp+3552], xmm0
	lea esp, [esp+3568]
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
