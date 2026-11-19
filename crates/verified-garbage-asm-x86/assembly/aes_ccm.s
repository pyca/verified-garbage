// The functions of `src/aes_ccm.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ccm_seal_aesni:
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
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 14
	sub eax, DWORD PTR [ebp+156]
	mov BYTE PTR [ebp+48], al
	mov edi, DWORD PTR [ebp+152]
	mov edx, ebp
	add edx, 49
	mov ecx, DWORD PTR [ebp+156]
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [ebp+180]
	sub eax, 2
	add eax, eax
	add eax, eax
	mov ecx, 14
	sub ecx, DWORD PTR [ebp+156]
	add eax, ecx
	mov ecx, DWORD PTR [ebp+164]
	test ecx, ecx
	je 21f
	add eax, 64
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+36], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+40], ecx
	mov BYTE PTR [ebp+32], al
	mov eax, DWORD PTR [ebp+172]
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+276], eax
	test eax, eax
	je 23f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+276]
	cmp eax, 65280
	jb 25f
	mov ecx, 65279
	mov DWORD PTR [ebp+32], ecx
	bswap eax
	mov DWORD PTR [ebp+34], eax
	mov eax, 6
	mov DWORD PTR [ebp+280], eax
	jmp 26f
25:
	bswap eax
	shr eax, 16
	mov DWORD PTR [ebp+32], eax
	mov eax, 2
	mov DWORD PTR [ebp+280], eax
26:
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 27f
	jmp 28f
27:
	mov ecx, eax
28:
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 210f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 211f
210:
211:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 212f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 213f
212:
213:
	jmp 24f
23:
24:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 218f
217:
218:
	mov eax, 0
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 220f
	mov eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	add ebp, 384
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
	sub ebp, 384
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 222f
	mov eax, DWORD PTR [ebp+172]
	shr eax, 4
	add eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 80
	mov ecx, DWORD PTR [ebp+276]
224:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	jmp 223f
222:
223:
	mov edi, ebp
	mov edx, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+180]
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2668]
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
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	lea esp, [esp+2668]
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

vg_aes_ccm_open_aesni:
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
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 14
	sub eax, DWORD PTR [ebp+156]
	mov BYTE PTR [ebp+48], al
	mov edi, DWORD PTR [ebp+152]
	mov edx, ebp
	add edx, 49
	mov ecx, DWORD PTR [ebp+156]
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 21f
	mov eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	add ebp, 384
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
	sub ebp, 384
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 23f
	mov eax, DWORD PTR [ebp+172]
	shr eax, 4
	add eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 80
	mov ecx, DWORD PTR [ebp+276]
25:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [ebp+180]
	sub eax, 2
	add eax, eax
	add eax, eax
	mov ecx, 14
	sub ecx, DWORD PTR [ebp+156]
	add eax, ecx
	mov ecx, DWORD PTR [ebp+164]
	test ecx, ecx
	je 26f
	add eax, 64
	jmp 27f
26:
27:
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+36], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+40], ecx
	mov BYTE PTR [ebp+32], al
	mov eax, DWORD PTR [ebp+172]
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+276], eax
	test eax, eax
	je 28f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+276]
	cmp eax, 65280
	jb 210f
	mov ecx, 65279
	mov DWORD PTR [ebp+32], ecx
	bswap eax
	mov DWORD PTR [ebp+34], eax
	mov eax, 6
	mov DWORD PTR [ebp+280], eax
	jmp 211f
210:
	bswap eax
	shr eax, 16
	mov DWORD PTR [ebp+32], eax
	mov eax, 2
	mov DWORD PTR [ebp+280], eax
211:
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 212f
	jmp 213f
212:
	mov ecx, eax
213:
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 218f
217:
218:
	jmp 29f
28:
29:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 220f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 222f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
224:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 223f
222:
223:
	mov eax, 0
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 96
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
226:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+172]
	test ecx, ecx
	je 227f
	mov ebx, 0
	sub ebx, DWORD PTR [ebp+176]
	mov edi, DWORD PTR [ebp+168]
	cmp ecx, 4
	jb 229f
231:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 231b
	jmp 230f
229:
230:
	test ecx, ecx
	je 232f
234:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 234b
	jmp 233f
232:
233:
	jmp 228f
227:
228:
	mov eax, DWORD PTR [ebp+176]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2668]
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
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	lea esp, [esp+2668]
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

vg_aes_ccm_seal:
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
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 14
	sub eax, DWORD PTR [ebp+156]
	mov BYTE PTR [ebp+48], al
	mov edi, DWORD PTR [ebp+152]
	mov edx, ebp
	add edx, 49
	mov ecx, DWORD PTR [ebp+156]
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [ebp+180]
	sub eax, 2
	add eax, eax
	add eax, eax
	mov ecx, 14
	sub ecx, DWORD PTR [ebp+156]
	add eax, ecx
	mov ecx, DWORD PTR [ebp+164]
	test ecx, ecx
	je 21f
	add eax, 64
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+36], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+40], ecx
	mov BYTE PTR [ebp+32], al
	mov eax, DWORD PTR [ebp+172]
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+276], eax
	test eax, eax
	je 23f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+276]
	cmp eax, 65280
	jb 25f
	mov ecx, 65279
	mov DWORD PTR [ebp+32], ecx
	bswap eax
	mov DWORD PTR [ebp+34], eax
	mov eax, 6
	mov DWORD PTR [ebp+280], eax
	jmp 26f
25:
	bswap eax
	shr eax, 16
	mov DWORD PTR [ebp+32], eax
	mov eax, 2
	mov DWORD PTR [ebp+280], eax
26:
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 27f
	jmp 28f
27:
	mov ecx, eax
28:
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 210f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 211f
210:
211:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 212f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 213f
212:
213:
	jmp 24f
23:
24:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 0
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 218f
217:
218:
	mov eax, 0
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 0
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 220f
	mov eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	add ebp, 384
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
	sub ebp, 384
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 222f
	mov eax, DWORD PTR [ebp+172]
	shr eax, 4
	add eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 80
	mov ecx, DWORD PTR [ebp+276]
224:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	jmp 223f
222:
223:
	mov edi, ebp
	mov edx, DWORD PTR [ebp+212]
	mov ecx, DWORD PTR [ebp+180]
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2668]
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
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	lea esp, [esp+2668]
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

vg_aes_ccm_open:
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
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+212], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+180], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 14
	sub eax, DWORD PTR [ebp+156]
	mov BYTE PTR [ebp+48], al
	mov edi, DWORD PTR [ebp+152]
	mov edx, ebp
	add edx, 49
	mov ecx, DWORD PTR [ebp+156]
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 21f
	mov eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	add ebp, 384
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
	sub ebp, 384
	jmp 22f
21:
22:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 23f
	mov eax, DWORD PTR [ebp+172]
	shr eax, 4
	add eax, 1
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 80
	mov ecx, DWORD PTR [ebp+276]
25:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [ebp+180]
	sub eax, 2
	add eax, eax
	add eax, eax
	mov ecx, 14
	sub ecx, DWORD PTR [ebp+156]
	add eax, ecx
	mov ecx, DWORD PTR [ebp+164]
	test ecx, ecx
	je 26f
	add eax, 64
	jmp 27f
26:
27:
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+36], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+40], ecx
	mov BYTE PTR [ebp+32], al
	mov eax, DWORD PTR [ebp+172]
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+96], eax
	mov DWORD PTR [ebp+100], eax
	mov DWORD PTR [ebp+104], eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+276], eax
	test eax, eax
	je 28f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [ebp+276]
	cmp eax, 65280
	jb 210f
	mov ecx, 65279
	mov DWORD PTR [ebp+32], ecx
	bswap eax
	mov DWORD PTR [ebp+34], eax
	mov eax, 6
	mov DWORD PTR [ebp+280], eax
	jmp 211f
210:
	bswap eax
	shr eax, 16
	mov DWORD PTR [ebp+32], eax
	mov eax, 2
	mov DWORD PTR [ebp+280], eax
211:
	mov ecx, 16
	sub ecx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	cmp eax, ecx
	jb 212f
	jmp 213f
212:
	mov ecx, eax
213:
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	add edx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+276]
	sub eax, ecx
	mov DWORD PTR [ebp+276], eax
	mov eax, edi
	add eax, ecx
	mov DWORD PTR [ebp+272], eax
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 218f
217:
218:
	jmp 29f
28:
29:
	mov eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+272], eax
	mov eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+276], eax
	mov ebx, DWORD PTR [ebp+272]
	mov edi, DWORD PTR [ebp+276]
	shr edi, 4
	mov eax, DWORD PTR [ebp+276]
	mov edx, eax
	and edx, 15
	mov DWORD PTR [ebp+276], edx
	sub eax, edx
	add eax, ebx
	mov DWORD PTR [ebp+272], eax
	test edi, edi
	je 220f
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov esi, edi
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 221f
220:
221:
	mov ecx, DWORD PTR [ebp+276]
	test ecx, ecx
	je 222f
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov edi, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+276]
224:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 224b
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 32
	mov esi, 1
	mov edi, ebp
	add edi, 384
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 223f
222:
223:
	mov eax, 0
	mov ecx, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+64], ecx
	mov ecx, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+68], ecx
	mov ecx, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+72], ecx
	bswap eax
	or eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+144]
	mov ecx, DWORD PTR [ebp+148]
	mov edx, ebp
	add edx, 64
	mov ebx, ebp
	add ebx, 96
	mov edi, 1
	add ebp, 384
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
	sub ebp, 384
	mov eax, 0
	mov DWORD PTR [ebp+196], eax
	mov DWORD PTR [ebp+200], eax
	mov DWORD PTR [ebp+204], eax
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+212]
	mov edx, ebp
	add edx, 196
	mov ecx, DWORD PTR [ebp+180]
225:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 225b
	mov eax, 0
	mov DWORD PTR [ebp+240], eax
	mov DWORD PTR [ebp+244], eax
	mov DWORD PTR [ebp+248], eax
	mov DWORD PTR [ebp+252], eax
	mov edi, ebp
	add edi, 96
	mov edx, ebp
	add edx, 240
	mov ecx, DWORD PTR [ebp+180]
226:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
	mov eax, DWORD PTR [ebp+240]
	xor eax, DWORD PTR [ebp+196]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, DWORD PTR [ebp+200]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, DWORD PTR [ebp+204]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, DWORD PTR [ebp+208]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+176], eax
	mov ecx, DWORD PTR [ebp+172]
	test ecx, ecx
	je 227f
	mov ebx, 0
	sub ebx, DWORD PTR [ebp+176]
	mov edi, DWORD PTR [ebp+168]
	cmp ecx, 4
	jb 229f
231:
	mov edx, DWORD PTR [edi]
	and edx, ebx
	mov DWORD PTR [edi], edx
	add edi, 4
	sub ecx, 4
	cmp ecx, 4
	jae 231b
	jmp 230f
229:
230:
	test ecx, ecx
	je 232f
234:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 234b
	jmp 233f
232:
233:
	jmp 228f
227:
228:
	mov eax, DWORD PTR [ebp+176]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-2668]
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
	mov DWORD PTR [esp+2656], ecx
	mov DWORD PTR [esp+2660], ecx
	mov DWORD PTR [esp+2664], ecx
	lea esp, [esp+2668]
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
