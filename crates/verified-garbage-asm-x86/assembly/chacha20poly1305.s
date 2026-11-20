// The functions of `src/chacha20poly1305.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_ssse3:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, DWORD PTR [esp+28]
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+740]
	pxor xmm0, xmm0
	lea esp, [esp-1280]
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
	lea esp, [esp+1280]
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

vg_chacha20_poly1305_open_ssse3:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, edi
	add ecx, 16
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edx]
	mov ecx, DWORD PTR [edi+20]
	xor ecx, DWORD PTR [edx+4]
	or eax, ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edx+8]
	or eax, ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edx+12]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	cmp eax, 0
	je 26f
	jmp 27f
26:
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+24]
	cmp edx, 0
	je 28f
210:
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub edx, 1
	jne 210b
	jmp 29f
28:
29:
27:
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+740]
	pxor xmm0, xmm0
	lea esp, [esp-1280]
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
	lea esp, [esp+1280]
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

vg_chacha20_poly1305_open_to_ssse3:
	lea esp, [esp-748]
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+772]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+776]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+780]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+784]
	mov DWORD PTR [esp+36], eax
	mov eax, esp
	add eax, 44
	mov DWORD PTR [esp+40], eax
	mov ecx, DWORD PTR [esp+28]
	mov edx, DWORD PTR [esp+36]
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+28], edx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, edi
	add ecx, 16
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edx]
	mov ecx, DWORD PTR [edi+20]
	xor ecx, DWORD PTR [edx+4]
	or eax, ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edx+8]
	or eax, ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edx+12]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	cmp eax, 0
	je 26f
	jmp 27f
26:
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+24]
	cmp edx, 0
	je 28f
210:
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub edx, 1
	jne 210b
	jmp 29f
28:
29:
27:
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+748]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1288]
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
	mov DWORD PTR [esp+1280], ecx
	mov DWORD PTR [esp+1284], ecx
	lea esp, [esp+1288]
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

vg_chacha20_poly1305_seal_gather_ssse3:
	lea esp, [esp-48]
	mov DWORD PTR [esp+36], ebx
	mov DWORD PTR [esp+40], esi
	mov DWORD PTR [esp+44], edi
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+24], eax
	mov esi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [esp+72]
	mov edx, DWORD PTR [esp+76]
	cmp ebx, 0
	je 20f
22:
	mov edi, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+4]
	shr ecx, 4
	cmp ecx, 0
	je 23f
25:
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edx], xmm0
	add edi, 16
	add edx, 16
	sub ecx, 1
	jne 25b
	jmp 24f
23:
24:
	mov ecx, DWORD PTR [esi+4]
	shr ecx, 2
	and ecx, 3
	je 26f
28:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edx], eax
	add edi, 4
	add edx, 4
	sub ecx, 1
	jne 28b
	jmp 27f
26:
27:
	mov ecx, DWORD PTR [esi+4]
	and ecx, 3
	je 29f
211:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	jmp 210f
29:
210:
	add esi, 8
	sub ebx, 1
	jne 22b
	jmp 21f
20:
21:
	call {vg_chacha20_poly1305_seal_core_ssse3}
	mov ebx, DWORD PTR [esp+36]
	mov esi, DWORD PTR [esp+40]
	mov edi, DWORD PTR [esp+44]
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1332]
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
	mov DWORD PTR [esp+1328], ecx
	lea esp, [esp+1332]
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

vg_chacha20_poly1305_seal:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, DWORD PTR [esp+28]
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+740]
	pxor xmm0, xmm0
	lea esp, [esp-1280]
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
	lea esp, [esp+1280]
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

vg_chacha20_poly1305_open:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, edi
	add ecx, 16
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edx]
	mov ecx, DWORD PTR [edi+20]
	xor ecx, DWORD PTR [edx+4]
	or eax, ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edx+8]
	or eax, ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edx+12]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	cmp eax, 0
	je 26f
	jmp 27f
26:
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+24]
	cmp edx, 0
	je 28f
210:
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub edx, 1
	jne 210b
	jmp 29f
28:
29:
27:
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+740]
	pxor xmm0, xmm0
	lea esp, [esp-1280]
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
	lea esp, [esp+1280]
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

vg_chacha20_poly1305_open_to:
	lea esp, [esp-748]
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+772]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+776]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+780]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+784]
	mov DWORD PTR [esp+36], eax
	mov eax, esp
	add eax, 44
	mov DWORD PTR [esp+40], eax
	mov ecx, DWORD PTR [esp+28]
	mov edx, DWORD PTR [esp+36]
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp+28], edx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov eax, 1634760805
	mov DWORD PTR [edi+64], eax
	mov eax, 857760878
	mov DWORD PTR [edi+68], eax
	mov eax, 2036477234
	mov DWORD PTR [edi+72], eax
	mov eax, 1797285236
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edx]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edx+4]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edx+8]
	mov DWORD PTR [edi+124], eax
	mov ecx, edi
	add ecx, 64
	mov edx, edi
	add edx, 128
	push edx
	push ecx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, edi
	add ecx, 128
	mov edx, edi
	add edx, 448
	push ecx
	push edx
	call {vg_poly1305_init_core}
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 20f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 22b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [esp+24]
	mov eax, ebp
	shr eax, 4
	mov ecx, edi
	add ecx, 448
	push eax
	push ebx
	push ecx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov edx, ebp
	and edx, 15
	je 23f
	mov esi, ebp
	sub esi, edx
	add esi, ebx
	mov eax, 0
	mov DWORD PTR [edi+48], eax
	mov DWORD PTR [edi+52], eax
	mov DWORD PTR [edi+56], eax
	mov DWORD PTR [edi+60], eax
	mov ecx, edi
	add ecx, 48
25:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ecx], al
	add esi, 1
	add ecx, 1
	sub edx, 1
	jne 25b
	mov eax, 1
	mov ecx, edi
	add ecx, 48
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [edi+40], eax
	mov eax, 0
	mov DWORD PTR [edi+36], eax
	mov DWORD PTR [edi+44], eax
	mov eax, 1
	mov ecx, edi
	add ecx, 32
	mov edx, edi
	add edx, 448
	push eax
	push ecx
	push edx
	call {vg_poly1305_blocks}
	pop eax
	pop eax
	pop eax
	mov eax, 1
	mov DWORD PTR [edi+112], eax
	mov eax, edi
	add eax, 64
	mov ecx, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+24]
	mov ebx, edi
	add ebx, 128
	mov esi, DWORD PTR [esp+32]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_chacha20_xor}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, edi
	add ebx, 576
	mov ecx, edi
	add ecx, 16
	mov eax, 0
	mov esi, edi
	add esi, 448
	push ebx
	push ecx
	push eax
	push eax
	push esi
	call {vg_poly1305_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edx]
	mov ecx, DWORD PTR [edi+20]
	xor ecx, DWORD PTR [edx+4]
	or eax, ecx
	mov ecx, DWORD PTR [edi+24]
	xor ecx, DWORD PTR [edx+8]
	or eax, ecx
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edx+12]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	cmp eax, 0
	je 26f
	jmp 27f
26:
	mov ecx, DWORD PTR [esp+32]
	mov edx, DWORD PTR [esp+24]
	cmp edx, 0
	je 28f
210:
	mov BYTE PTR [ecx], al
	add ecx, 1
	sub edx, 1
	jne 210b
	jmp 29f
28:
29:
27:
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+4]
	mov ebp, DWORD PTR [edi+12]
	mov edi, DWORD PTR [edi+8]
	lea esp, [esp+748]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1288]
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
	mov DWORD PTR [esp+1280], ecx
	mov DWORD PTR [esp+1284], ecx
	lea esp, [esp+1288]
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

vg_chacha20_poly1305_seal_gather:
	lea esp, [esp-48]
	mov DWORD PTR [esp+36], ebx
	mov DWORD PTR [esp+40], esi
	mov DWORD PTR [esp+44], edi
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+24], eax
	mov esi, DWORD PTR [esp+68]
	mov ebx, DWORD PTR [esp+72]
	mov edx, DWORD PTR [esp+76]
	cmp ebx, 0
	je 20f
22:
	mov edi, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+4]
	shr ecx, 4
	cmp ecx, 0
	je 23f
25:
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edx], xmm0
	add edi, 16
	add edx, 16
	sub ecx, 1
	jne 25b
	jmp 24f
23:
24:
	mov ecx, DWORD PTR [esi+4]
	shr ecx, 2
	and ecx, 3
	je 26f
28:
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edx], eax
	add edi, 4
	add edx, 4
	sub ecx, 1
	jne 28b
	jmp 27f
26:
27:
	mov ecx, DWORD PTR [esi+4]
	and ecx, 3
	je 29f
211:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 211b
	jmp 210f
29:
210:
	add esi, 8
	sub ebx, 1
	jne 22b
	jmp 21f
20:
21:
	call {vg_chacha20_poly1305_seal_core}
	mov ebx, DWORD PTR [esp+36]
	mov esi, DWORD PTR [esp+40]
	mov edi, DWORD PTR [esp+44]
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1332]
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
	mov DWORD PTR [esp+1328], ecx
	lea esp, [esp+1332]
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
