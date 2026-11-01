// The functions of `src/blowfish_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_ofb:
	lea esp, [esp-112]
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+128]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+48], ebx
	mov DWORD PTR [eax+52], esi
	mov DWORD PTR [eax+56], edi
	mov DWORD PTR [eax+60], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+68], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+44], eax
	mov ebp, edi
	mov ebx, ebp
	add ebx, 40
	mov DWORD PTR [ebp+32], ebx
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebp+40], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebp+44], eax
	mov edi, ebp
	mov esi, DWORD PTR [edi+64]
	mov ebp, DWORD PTR [edi+68]
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+64], esi
	mov DWORD PTR [edi+68], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+48]
	mov esi, DWORD PTR [edi+52]
	mov ebp, DWORD PTR [edi+60]
	mov edi, DWORD PTR [edi+56]
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
	lea esp, [esp+112]
	ret
	.p2align 6
