// The functions of `src/hmac_md5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init:
	mov eax, DWORD PTR [esp+16]
	cmp eax, 65
	jae 20f
	lea esp, [esp-408]
	mov eax, DWORD PTR [esp+412]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+416]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+420]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+424]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_md5_init_core}
	pop eax
	push esi
	call {vg_md5_init_core}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+16], ecx
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], ecx
	mov DWORD PTR [ebx+28], ecx
	mov DWORD PTR [ebx+32], ecx
	mov DWORD PTR [ebx+36], ecx
	mov DWORD PTR [ebx+40], ecx
	mov DWORD PTR [ebx+44], ecx
	mov DWORD PTR [ebx+48], ecx
	mov DWORD PTR [ebx+52], ecx
	mov DWORD PTR [ebx+56], ecx
	mov DWORD PTR [ebx+60], ecx
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 16
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
	mov eax, DWORD PTR [ebx+16]
	xor eax, 1785358954
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [ebx+20]
	xor eax, 1785358954
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [ebx+24]
	xor eax, 1785358954
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [ebx+28]
	xor eax, 1785358954
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [ebx+32]
	xor eax, 1785358954
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [ebx+36]
	xor eax, 1785358954
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [ebx+40]
	xor eax, 1785358954
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [ebx+44]
	xor eax, 1785358954
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [ebx+48]
	xor eax, 1785358954
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [ebx+52]
	xor eax, 1785358954
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [ebx+56]
	xor eax, 1785358954
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [ebx+60]
	xor eax, 1785358954
	mov DWORD PTR [esi+60], eax
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
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+408]
21:
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1124]
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
	mov DWORD PTR [esp+1120], ecx
	lea esp, [esp+1124]
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
	lea esp, [esp-1048]
	mov eax, DWORD PTR [esp+1052]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1056]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1060]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1064]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+384], ebx
	mov DWORD PTR [eax+388], esi
	mov DWORD PTR [eax+392], edi
	mov DWORD PTR [eax+396], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	cmp ecx, 65
	jae 25f
	mov edx, DWORD PTR [esp+12]
	jmp 26f
25:
	mov edi, ebp
	add edi, 640
	push edi
	call {vg_md5_init_core}
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
	call {vg_md5_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, 0
	mov edx, ebp
	add edx, 752
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_md5_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	add edx, 752
	mov ecx, 16
26:
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_md5_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+384]
	mov esi, DWORD PTR [eax+388]
	mov edi, DWORD PTR [eax+392]
	mov ebp, DWORD PTR [eax+396]
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
	lea esp, [esp+1048]
	jmp 21b
	.p2align 6

vg_hmac_md5_finalize:
	lea esp, [esp-412]
	mov eax, DWORD PTR [esp+416]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+420]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+424]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+428]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+432]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+112], ebx
	mov DWORD PTR [eax+116], esi
	mov DWORD PTR [eax+120], edi
	mov DWORD PTR [eax+124], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebp
	add edx, 128
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_md5_finalize_scratch}
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
	mov ecx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebx+16], ecx
	mov ecx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [ebp+136]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+32], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+52], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 640
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov eax, ebx
	add eax, 16
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_md5_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+112]
	mov esi, DWORD PTR [eax+116]
	mov edi, DWORD PTR [eax+120]
	mov ebp, DWORD PTR [eax+124]
	lea esp, [esp+412]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-460]
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
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	lea esp, [esp+460]
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
