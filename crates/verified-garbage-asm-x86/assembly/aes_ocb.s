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
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
216:
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
	je 217f
	jmp 218f
217:
219:
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
	je 219b
218:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 216b
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
220:
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
	je 221f
	jmp 222f
221:
223:
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
	je 223b
222:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 220b
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
	je 224f
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
226:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
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
227:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	jmp 225f
224:
225:
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
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
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
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
216:
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
	je 217f
	jmp 218f
217:
219:
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
	je 219b
218:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 216b
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
220:
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
	je 221f
	jmp 222f
221:
223:
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
	je 223b
222:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+44], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 220b
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
	je 224f
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
226:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
227:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
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
	jmp 225f
224:
225:
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
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
229:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 229b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	test ecx, ecx
	je 230f
232:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
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
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
216:
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
	je 217f
	jmp 218f
217:
219:
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
	je 219b
218:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+44], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 216b
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
220:
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
	je 221f
	jmp 222f
221:
223:
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
	je 223b
222:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 220b
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
	je 224f
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
226:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
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
227:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
	jmp 225f
224:
225:
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
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
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
	mov esi, DWORD PTR [ebp+200]
	mov ebx, DWORD PTR [ebp+280]
	mov edi, 1
216:
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
	je 217f
	jmp 218f
217:
219:
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
	je 219b
218:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 216b
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
220:
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
	je 221f
	jmp 222f
221:
223:
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
	je 223b
222:
	mov eax, DWORD PTR [ebp+16]
	xor eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+20], eax
	mov eax, DWORD PTR [ebp+24]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+24], eax
	mov eax, DWORD PTR [ebp+28]
	xor eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [ebp+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [ebp+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [ebp+28]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebp+32]
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [ebp+32], eax
	mov eax, DWORD PTR [ebp+36]
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [ebp+36], eax
	mov eax, DWORD PTR [ebp+40]
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+44]
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [ebp+44], eax
	add esi, 16
	add edi, 1
	sub ebx, 1
	jne 220b
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
	je 224f
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
226:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 226b
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov edi, esi
	mov edx, ebp
	add edx, 144
	mov ecx, DWORD PTR [ebp+276]
227:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 227b
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
	jmp 225f
224:
225:
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
228:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 228b
	mov edx, 0
	mov edi, ebp
	mov ecx, DWORD PTR [ebp+212]
229:
	movzx eax, BYTE PTR [edi]
	movzx ebx, BYTE PTR [edi+144]
	xor eax, ebx
	or edx, eax
	add edi, 1
	sub ecx, 1
	jne 229b
	sub edx, 1
	shr edx, 31
	mov DWORD PTR [ebp+284], edx
	mov edi, DWORD PTR [ebp+200]
	mov ecx, DWORD PTR [ebp+204]
	mov edx, 0
	sub edx, DWORD PTR [ebp+284]
	test ecx, ecx
	je 230f
232:
	movzx eax, BYTE PTR [edi]
	and eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	sub ecx, 1
	jne 232b
	jmp 231f
230:
231:
	mov eax, DWORD PTR [ebp+284]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2608]
	ret
	.p2align 6
