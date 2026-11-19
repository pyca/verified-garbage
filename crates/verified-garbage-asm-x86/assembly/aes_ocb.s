// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init_aesni:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, DWORD PTR [ebp+176]
	add ebp, 512
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edx, DWORD PTR [ebp+176]
	mov eax, 0
	mov DWORD PTR [edx+240], eax
	mov DWORD PTR [edx+244], eax
	mov DWORD PTR [edx+248], eax
	mov DWORD PTR [edx+252], eax
	mov eax, edx
	mov ecx, DWORD PTR [ebp+188]
	shr ecx, 2
	add ecx, 6
	add edx, 240
	mov ebx, 1
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2580]
	ret
	.p2align 6

vg_aes_ocb_seal_aesni:
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
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+12], eax
	mov edi, ebp
	mov edx, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	ret
	.p2align 6

vg_aes_ocb_open_aesni:
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
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+156], eax
	mov edi, DWORD PTR [ebp+208]
	mov edx, ebp
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
275:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 275b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	movd xmm0, edx
	pshufd xmm0, xmm0, 0
	mov eax, ecx
	shr eax, 4
	and ecx, 15
	test eax, eax
	je 276f
278:
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	add edi, 16
	sub eax, 1
	jne 278b
	jmp 277f
276:
277:
	test ecx, ecx
	je 279f
281:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 281b
	jmp 280f
279:
280:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	ret
	.p2align 6

vg_aes_ocb_init:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, DWORD PTR [ebp+176]
	add ebp, 512
	push ebp
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edx, DWORD PTR [ebp+176]
	mov eax, 0
	mov DWORD PTR [edx+240], eax
	mov DWORD PTR [edx+244], eax
	mov DWORD PTR [edx+248], eax
	mov DWORD PTR [edx+252], eax
	mov eax, edx
	mov ecx, DWORD PTR [ebp+188]
	shr ecx, 2
	add ecx, 6
	add edx, 240
	mov ebx, 1
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2580]
	ret
	.p2align 6

vg_aes_ocb_seal:
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
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp], eax
	mov eax, DWORD PTR [ebp+4]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+4], eax
	mov eax, DWORD PTR [ebp+8]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+8], eax
	mov eax, DWORD PTR [ebp+12]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+12], eax
	mov edi, ebp
	mov edx, DWORD PTR [ebp+208]
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	ret
	.p2align 6

vg_aes_ocb_open:
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
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [ebp+204], eax
	mov eax, DWORD PTR [esp+36]
	mov DWORD PTR [ebp+208], eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [ebp+212], eax
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebx+240]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+244]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebx+244]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+248]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebx+248]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebx+252]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebx+252]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+64]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+68]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+68]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+72]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+72]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+76]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+76]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+92], eax
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov edi, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 128
	sub edx, ecx
20:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 20b
	mov ecx, DWORD PTR [ebp+188]
	mov edx, ebp
	add edx, 127
	sub edx, ecx
	mov eax, 1
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+212]
	and eax, 15
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	movzx ecx, BYTE PTR [ebp+112]
	or ecx, eax
	mov BYTE PTR [ebp+112], cl
	movzx eax, BYTE PTR [ebp+127]
	mov ecx, eax
	and ecx, 63
	mov DWORD PTR [ebp+216], ecx
	and eax, 192
	mov BYTE PTR [ebp+127], al
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	bswap eax
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+116]
	bswap eax
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+120]
	bswap eax
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+124]
	bswap eax
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+256], ecx
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+260], ecx
	mov eax, DWORD PTR [ebp+216]
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+244]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+248]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+252]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+256]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	mov edx, DWORD PTR [ebp+260]
	shr edx, 31
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 31
	and ecx, -2
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 1
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+244]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+248]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+252]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+256]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	mov edx, DWORD PTR [ebp+260]
	shr edx, 30
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 30
	and ecx, -4
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 2
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+244]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+248]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+252]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+256]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	mov edx, DWORD PTR [ebp+260]
	shr edx, 28
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 28
	and ecx, -16
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 3
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+244]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+248]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+252]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+256]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	mov edx, DWORD PTR [ebp+260]
	shr edx, 24
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 24
	and ecx, -256
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 4
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+244]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+248]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+252]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+256]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	mov edx, DWORD PTR [ebp+260]
	shr edx, 16
	or ecx, edx
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, eax
	ror ecx, 16
	and ecx, -65536
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+216]
	shr eax, 5
	and eax, 1
	mov ebx, 0
	sub ebx, eax
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+240], eax
	mov eax, DWORD PTR [ebp+244]
	mov ecx, DWORD PTR [ebp+248]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+244], eax
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebp+252]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+248], eax
	mov eax, DWORD PTR [ebp+252]
	mov ecx, DWORD PTR [ebp+256]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+252], eax
	mov eax, DWORD PTR [ebp+256]
	mov ecx, DWORD PTR [ebp+260]
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+256], eax
	mov eax, DWORD PTR [ebp+260]
	mov ecx, 0
	xor ecx, eax
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+260], eax
	mov eax, DWORD PTR [ebp+240]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+224], eax
	mov eax, DWORD PTR [ebp+244]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+228], eax
	mov eax, DWORD PTR [ebp+248]
	bswap eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+232], eax
	mov eax, DWORD PTR [ebp+252]
	bswap eax
	mov DWORD PTR [ebp+28], eax
	mov DWORD PTR [ebp+236], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov eax, 0
	mov DWORD PTR [ebp+160], eax
	mov DWORD PTR [ebp+164], eax
	mov DWORD PTR [ebp+168], eax
	mov DWORD PTR [ebp+172], eax
	mov esi, DWORD PTR [ebp+192]
	mov eax, DWORD PTR [ebp+196]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	shr eax, 4
	mov DWORD PTR [ebp+264], eax
	mov edi, 1
	test eax, eax
	je 21f
23:
	mov ebx, DWORD PTR [ebp+264]
	cmp ebx, 8
	jb 24f
	mov ebx, 8
	jmp 25f
24:
25:
	mov DWORD PTR [ebp+272], ebx
	mov eax, ebp
	add eax, 384
	mov DWORD PTR [ebp+268], eax
26:
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 27f
	jmp 28f
27:
29:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 29b
28:
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+172], eax
	mov edx, DWORD PTR [ebp+268]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [edx+12], eax
	add edx, 16
	mov DWORD PTR [ebp+268], edx
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 26b
	mov edx, ebp
	add edx, 384
	mov ebx, DWORD PTR [ebp+272]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov ebx, DWORD PTR [ebp+272]
	mov edx, ebp
	add edx, 384
210:
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [ebp+60], eax
	add edx, 16
	sub ebx, 1
	jne 210b
	mov eax, DWORD PTR [ebp+264]
	sub eax, DWORD PTR [ebp+272]
	mov DWORD PTR [ebp+264], eax
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [ebp+276]
	test eax, eax
	je 211f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+172], eax
	mov eax, 0
	mov DWORD PTR [ebp+384], eax
	mov DWORD PTR [ebp+388], eax
	mov DWORD PTR [ebp+392], eax
	mov DWORD PTR [ebp+396], eax
	mov edi, esi
	mov edx, ebp
	add edx, 384
	mov ecx, DWORD PTR [ebp+276]
213:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 213b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+384]
	xor eax, DWORD PTR [ebp+160]
	mov DWORD PTR [ebp+384], eax
	mov eax, DWORD PTR [ebp+388]
	xor eax, DWORD PTR [ebp+164]
	mov DWORD PTR [ebp+388], eax
	mov eax, DWORD PTR [ebp+392]
	xor eax, DWORD PTR [ebp+168]
	mov DWORD PTR [ebp+392], eax
	mov eax, DWORD PTR [ebp+396]
	xor eax, DWORD PTR [ebp+172]
	mov DWORD PTR [ebp+396], eax
	mov edx, ebp
	add edx, 384
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+48]
	xor eax, DWORD PTR [ebp+384]
	mov DWORD PTR [ebp+48], eax
	mov eax, DWORD PTR [ebp+52]
	xor eax, DWORD PTR [ebp+388]
	mov DWORD PTR [ebp+52], eax
	mov eax, DWORD PTR [ebp+56]
	xor eax, DWORD PTR [ebp+392]
	mov DWORD PTR [ebp+56], eax
	mov eax, DWORD PTR [ebp+60]
	xor eax, DWORD PTR [ebp+396]
	mov DWORD PTR [ebp+60], eax
	jmp 212f
211:
212:
	mov ebx, DWORD PTR [ebp+204]
	shr ebx, 4
	mov DWORD PTR [ebp+280], ebx
	test ebx, ebx
	je 214f
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+288], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+292], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+296], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+300], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 2
	jb 216f
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+288]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+292]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+304], eax
	mov eax, DWORD PTR [ebp+292]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+296]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+308], eax
	mov eax, DWORD PTR [ebp+296]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+300]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+312], eax
	mov eax, DWORD PTR [ebp+300]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+316], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 4
	jb 218f
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+304]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+308]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+320], eax
	mov eax, DWORD PTR [ebp+308]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+312]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+324], eax
	mov eax, DWORD PTR [ebp+312]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+316]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+328], eax
	mov eax, DWORD PTR [ebp+316]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+332], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 8
	jb 220f
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+320]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+324]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+336], eax
	mov eax, DWORD PTR [ebp+324]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+328]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+340], eax
	mov eax, DWORD PTR [ebp+328]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+332]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+344], eax
	mov eax, DWORD PTR [ebp+332]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+348], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 16
	jb 222f
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+336]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+340]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+352], eax
	mov eax, DWORD PTR [ebp+340]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+344]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+356], eax
	mov eax, DWORD PTR [ebp+344]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+348]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+360], eax
	mov eax, DWORD PTR [ebp+348]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+364], eax
	mov eax, DWORD PTR [ebp+280]
	cmp eax, 32
	jb 224f
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+352]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+356]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+368], eax
	mov eax, DWORD PTR [ebp+356]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+360]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+372], eax
	mov eax, DWORD PTR [ebp+360]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+364]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+376], eax
	mov eax, DWORD PTR [ebp+364]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+380], eax
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 226f
228:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 229f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 231f
233:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 233b
	jmp 232f
231:
232:
	jmp 230f
229:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 234f
	jmp 235f
234:
236:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 236b
235:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
230:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 228b
	jmp 227f
226:
227:
	test ebx, ebx
	je 237f
239:
	mov eax, edi
	test eax, 63
	je 240f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 242f
244:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 244b
	jmp 243f
242:
243:
	jmp 241f
240:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 245f
	jmp 246f
245:
247:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 247b
246:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
241:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 239b
	jmp 238f
237:
238:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov edx, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+224]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+228]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+232]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+236]
	mov DWORD PTR [ebp+28], eax
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	cmp ebx, 4
	jb 248f
250:
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+304]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	movdqu xmm2, XMMWORD PTR [ebp+288]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	mov eax, edi
	test eax, 63
	je 251f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 253f
255:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 255b
	jmp 254f
253:
254:
	jmp 252f
251:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 256f
	jmp 257f
256:
258:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 258b
257:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
252:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 4
	cmp ebx, 4
	jae 250b
	jmp 249f
248:
249:
	test ebx, ebx
	je 259f
261:
	mov eax, edi
	test eax, 63
	je 262f
	mov edx, ebp
	add edx, 288
	test eax, 1
	jne 264f
266:
	add edx, 16
	shr eax, 1
	test eax, 1
	je 266b
	jmp 265f
264:
265:
	jmp 263f
262:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	mov eax, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], eax
	mov eax, edi
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 267f
	jmp 268f
267:
269:
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	shr eax, 31
	mov edx, 0
	sub edx, eax
	and edx, 135
	mov eax, DWORD PTR [ebp+96]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+100]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+100]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+104]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+104]
	bswap eax
	add eax, eax
	mov ecx, DWORD PTR [ebp+108]
	bswap ecx
	shr ecx, 31
	or eax, ecx
	bswap eax
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+108]
	bswap eax
	add eax, eax
	xor eax, edx
	bswap eax
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+220]
	shr eax, 1
	mov DWORD PTR [ebp+220], eax
	test eax, 1
	je 269b
268:
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebp+32]
	mov edx, ebp
	add edx, 96
263:
	movdqu xmm2, XMMWORD PTR [edx]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [esi], xmm3
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 261b
	jmp 260f
259:
260:
	movdqu XMMWORD PTR [ebp+16], xmm0
	movdqu XMMWORD PTR [ebp+32], xmm1
	jmp 215f
214:
215:
	mov esi, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+204]
	mov ecx, eax
	and ecx, 15
	mov DWORD PTR [ebp+276], ecx
	sub eax, ecx
	add esi, eax
	test ecx, ecx
	je 270f
	mov ebx, DWORD PTR [ebp+176]
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebx+240]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebx+244]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebx+248]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebx+252]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov edi, esi
	mov edx, ebp
	add edx, 112
	mov ecx, DWORD PTR [ebp+276]
272:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 272b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
273:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 273b
	mov eax, 128
	mov BYTE PTR [edx], al
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [ebp+148]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [ebp+152]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [ebp+156]
	mov DWORD PTR [ebp+44], eax
	jmp 271f
270:
271:
	mov eax, DWORD PTR [ebp+32]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+36]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+40]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+44]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+124]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+124], eax
	mov edx, ebp
	add edx, 112
	mov ebx, 1
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	add ebp, 512
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 512
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+156], eax
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [ebp+48]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [ebp+52]
	mov DWORD PTR [ebp+148], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [ebp+56]
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [ebp+60]
	mov DWORD PTR [ebp+156], eax
	mov edi, DWORD PTR [ebp+208]
	mov edx, ebp
	mov ecx, DWORD PTR [ebp+212]
274:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 274b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
275:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 275b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	movd xmm0, edx
	pshufd xmm0, xmm0, 0
	mov eax, ecx
	shr eax, 4
	and ecx, 15
	test eax, eax
	je 276f
278:
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	add edi, 16
	sub eax, 1
	jne 278b
	jmp 277f
276:
277:
	test ecx, ecx
	je 279f
281:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 281b
	jmp 280f
279:
280:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	ret
	.p2align 6
