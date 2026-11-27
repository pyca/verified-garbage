// The functions of `src/cast5_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_ofb_ssse3:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+592], ebx
	mov DWORD PTR [eax+596], esi
	mov DWORD PTR [eax+600], edi
	mov DWORD PTR [eax+604], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+612], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+608]
	mov ebp, DWORD PTR [edi+612]
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 23b
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 24f
	jmp 25f
24:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
25:
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+608]
	mov ecx, DWORD PTR [esi+612]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+608], eax
	mov DWORD PTR [esi+612], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+608]
	mov ebp, DWORD PTR [edi+612]
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+608], esi
	mov DWORD PTR [edi+612], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+592]
	mov esi, DWORD PTR [edi+596]
	mov ebp, DWORD PTR [edi+604]
	mov edi, DWORD PTR [edi+600]
	pxor xmm0, xmm0
	mov ecx, 0
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
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	lea esp, [esp+664]
	lea esp, [esp-672]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+668], ecx
	lea esp, [esp+672]
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

vg_cast5_ofb:
	lea esp, [esp-332]
	mov eax, DWORD PTR [esp+336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+264], ebx
	mov DWORD PTR [eax+268], esi
	mov DWORD PTR [eax+272], edi
	mov DWORD PTR [eax+276], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+284], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
24:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
25:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 25b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
26:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 26b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 23b
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 27f
	jmp 28f
27:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
29:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 29b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
28:
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+280]
	mov ecx, DWORD PTR [esi+284]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+280], eax
	mov DWORD PTR [esi+284], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+280], esi
	mov DWORD PTR [edi+284], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+264]
	mov esi, DWORD PTR [edi+268]
	mov ebp, DWORD PTR [edi+276]
	mov edi, DWORD PTR [edi+272]
	pxor xmm0, xmm0
	mov ecx, 0
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
	lea esp, [esp+332]
	lea esp, [esp-336]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	lea esp, [esp+336]
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

vg_cast5_ofb_final_ssse3:
	lea esp, [esp-664]
	mov eax, DWORD PTR [esp+668]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+672]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+676]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+592], ebx
	mov DWORD PTR [eax+596], esi
	mov DWORD PTR [eax+600], edi
	mov DWORD PTR [eax+604], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+612], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+608]
	mov ebp, DWORD PTR [edi+612]
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 23b
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 24f
	jmp 25f
24:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call {vg_cast5_lookup_ssse3}
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
25:
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+608]
	mov ecx, DWORD PTR [esi+612]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+608], eax
	mov DWORD PTR [esi+612], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+608]
	mov ebp, DWORD PTR [edi+612]
	cmp ebp, 8
	jb 26f
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+608], esi
	mov DWORD PTR [edi+612], ebp
	jmp 27f
26:
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+620], eax
	mov ebx, edi
	add ebx, 256
28:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 28b
	mov DWORD PTR [edi+608], esi
	mov DWORD PTR [edi+612], ebp
27:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+592]
	mov esi, DWORD PTR [edi+596]
	mov ebp, DWORD PTR [edi+604]
	mov edi, DWORD PTR [edi+600]
	pxor xmm0, xmm0
	mov ecx, 0
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
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	lea esp, [esp+664]
	lea esp, [esp-672]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+668], ecx
	lea esp, [esp+672]
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

vg_cast5_ofb_final:
	lea esp, [esp-332]
	mov eax, DWORD PTR [esp+336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+264], ebx
	mov DWORD PTR [eax+268], esi
	mov DWORD PTR [eax+272], edi
	mov DWORD PTR [eax+276], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+284], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
24:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
25:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 25b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
26:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 26b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 23b
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 27f
	jmp 28f
27:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234_STEPS}
	pop ecx
	mov ecx, eax
	mov edx, 16
	mov eax, -1
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	movdqa xmm6, xmm0
	pslld xmm6, 31
	psrld xmm6, 31
	paddd xmm6, xmm5
	pxor xmm6, xmm5
	movdqa xmm7, xmm0
	pslld xmm7, 30
	psrld xmm7, 31
	paddd xmm7, xmm5
	pxor xmm7, xmm5
	psrld xmm0, 2
	pxor xmm1, xmm1
29:
	movdqu xmm2, XMMWORD PTR [ecx]
	movdqu xmm3, XMMWORD PTR [ecx+16]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+32]
	movdqu xmm4, XMMWORD PTR [ecx+48]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+64]
	movdqu xmm3, XMMWORD PTR [ecx+80]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+96]
	movdqu xmm4, XMMWORD PTR [ecx+112]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+128]
	movdqu xmm3, XMMWORD PTR [ecx+144]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+160]
	movdqu xmm4, XMMWORD PTR [ecx+176]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ecx+192]
	movdqu xmm3, XMMWORD PTR [ecx+208]
	pand xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ecx+224]
	movdqu xmm4, XMMWORD PTR [ecx+240]
	pand xmm4, xmm6
	pxor xmm3, xmm4
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pandn xmm3, xmm2
	pxor xmm1, xmm3
	paddd xmm0, xmm5
	add ecx, 256
	sub edx, 1
	jne 29b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
28:
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+280]
	mov ecx, DWORD PTR [esi+284]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+280], eax
	mov DWORD PTR [esi+284], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	cmp ebp, 8
	jb 210f
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+280], esi
	mov DWORD PTR [edi+284], ebp
	jmp 211f
210:
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+292], eax
	mov ebx, edi
	add ebx, 256
212:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 212b
	mov DWORD PTR [edi+280], esi
	mov DWORD PTR [edi+284], ebp
211:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+264]
	mov esi, DWORD PTR [edi+268]
	mov ebp, DWORD PTR [edi+276]
	mov edi, DWORD PTR [edi+272]
	pxor xmm0, xmm0
	mov ecx, 0
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
	lea esp, [esp+332]
	lea esp, [esp-336]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	lea esp, [esp+336]
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
