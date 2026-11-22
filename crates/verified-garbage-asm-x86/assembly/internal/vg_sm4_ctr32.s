// The functions of `src/internal/vg_sm4_ctr32.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
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
	mov eax, DWORD PTR [edi+1452]
	cmp eax, 8
	jb 20f
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
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
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
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+320]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+324]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+328]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+332]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+336]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+340]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+344]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+348]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+352]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+356]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+360]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+364]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+368]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+372]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+376]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+380]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	cmp ebp, 8
	jae 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [edi+1452]
	cmp eax, 4
	jb 23f
25:
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
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
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
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+296]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+300]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+304]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+308]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+312]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+316]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	cmp ebp, 4
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+1452]
	cmp eax, 2
	jb 26f
28:
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
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
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
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+272]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+276]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+280]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+284]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1448], esi
	mov DWORD PTR [edi+1452], ebp
	cmp ebp, 2
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+1452]
	test eax, eax
	je 29f
211:
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
	mov eax, DWORD PTR [edi+1468]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1468], eax
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
	jne 211b
	jmp 210f
29:
210:
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
	ret
	.p2align 6
