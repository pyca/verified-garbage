// The functions of `src/internal/vg_aes_encrypt_blocks.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_encrypt_blocks:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	add ecx, 16
	mov edx, DWORD PTR [esp+8]
	sub edx, 1
	mov esi, edi
	add esi, 384
20:
	movdqu xmm0, XMMWORD PTR [ecx]
	mov eax, 1667457891
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	pxor xmm0, xmm7
	mov eax, -16711936
	movd xmm6, eax
	punpcklqdq xmm6, xmm6
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pshufd xmm0, xmm0, 216
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	mov eax, 1431655765
	movd xmm4, eax
	pshufd xmm4, xmm4, 0
	mov eax, 858993459
	movd xmm5, eax
	pshufd xmm5, xmm5, 0
	mov eax, 252645135
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 1
	pxor xmm7, xmm0
	pand xmm7, xmm4
	movdqa xmm1, xmm0
	pxor xmm1, xmm7
	psllq xmm7, 1
	pxor xmm0, xmm7
	movdqa xmm7, xmm1
	psrlq xmm7, 2
	pxor xmm7, xmm1
	pand xmm7, xmm5
	movdqa xmm2, xmm1
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm1, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 4
	pxor xmm7, xmm2
	pand xmm7, xmm6
	movdqa xmm3, xmm2
	pxor xmm3, xmm7
	psllq xmm7, 4
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+48], xmm2
	movdqu XMMWORD PTR [esi+112], xmm3
	movdqa xmm7, xmm1
	psrlq xmm7, 4
	pxor xmm7, xmm1
	pand xmm7, xmm6
	movdqa xmm3, xmm1
	pxor xmm3, xmm7
	psllq xmm7, 4
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu XMMWORD PTR [esi+80], xmm3
	movdqa xmm7, xmm0
	psrlq xmm7, 2
	pxor xmm7, xmm0
	pand xmm7, xmm5
	movdqa xmm2, xmm0
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm0, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 4
	pxor xmm7, xmm2
	pand xmm7, xmm6
	movdqa xmm3, xmm2
	pxor xmm3, xmm7
	psllq xmm7, 4
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu XMMWORD PTR [esi+96], xmm3
	movdqa xmm7, xmm0
	psrlq xmm7, 4
	pxor xmm7, xmm0
	pand xmm7, xmm6
	movdqa xmm3, xmm0
	pxor xmm3, xmm7
	psllq xmm7, 4
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu XMMWORD PTR [esi+64], xmm3
	add ecx, 16
	add esi, 128
	sub edx, 1
	jne 20b
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	test ebp, ebp
	je 21f
23:
	mov esi, ebx
	mov edx, edi
	cmp ebp, 8
	jae 24f
	mov ecx, ebp
	jmp 25f
24:
	mov ecx, 8
25:
26:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu XMMWORD PTR [edx], xmm0
	add esi, 16
	add edx, 16
	sub ecx, 1
	jne 26b
	mov ecx, DWORD PTR [esp+4]
	movdqu xmm5, XMMWORD PTR [ecx]
	mov eax, -16711936
	movd xmm6, eax
	punpcklqdq xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [edi+64]
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pshufd xmm0, xmm0, 216
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	psrlq xmm7, 24
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 24
	pxor xmm1, xmm7
	pshufd xmm1, xmm1, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	movdqu xmm2, XMMWORD PTR [edi+96]
	pxor xmm2, xmm5
	movdqa xmm7, xmm2
	psrlq xmm7, 24
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 24
	pxor xmm2, xmm7
	pshufd xmm2, xmm2, 216
	pshuflw xmm2, xmm2, 216
	pshufhw xmm2, xmm2, 216
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm5
	movdqa xmm7, xmm3
	psrlq xmm7, 24
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 24
	pxor xmm3, xmm7
	pshufd xmm3, xmm3, 216
	pshuflw xmm3, xmm3, 216
	pshufhw xmm3, xmm3, 216
	mov eax, 1431655765
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 1
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 1
	pxor xmm0, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 1
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 1
	pxor xmm2, xmm7
	mov eax, 858993459
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 2
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm0, xmm7
	movdqa xmm7, xmm1
	psrlq xmm7, 2
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 2
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+112], xmm3
	movdqu xmm5, XMMWORD PTR [ecx]
	mov eax, -16711936
	movd xmm6, eax
	punpcklqdq xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [edi]
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pshufd xmm0, xmm0, 216
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	psrlq xmm7, 24
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 24
	pxor xmm1, xmm7
	pshufd xmm1, xmm1, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	movdqu xmm2, XMMWORD PTR [edi+32]
	pxor xmm2, xmm5
	movdqa xmm7, xmm2
	psrlq xmm7, 24
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 24
	pxor xmm2, xmm7
	pshufd xmm2, xmm2, 216
	pshuflw xmm2, xmm2, 216
	pshufhw xmm2, xmm2, 216
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm5
	movdqa xmm7, xmm3
	psrlq xmm7, 24
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 24
	pxor xmm3, xmm7
	pshufd xmm3, xmm3, 216
	pshuflw xmm3, xmm3, 216
	pshufhw xmm3, xmm3, 216
	mov eax, 1431655765
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 1
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 1
	pxor xmm0, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 1
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 1
	pxor xmm2, xmm7
	mov eax, 858993459
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 2
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm0, xmm7
	movdqa xmm7, xmm1
	psrlq xmm7, 2
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 2
	pxor xmm1, xmm7
	mov eax, 252645135
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm7, xmm0
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm7, xmm1
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+16], xmm1
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm4, XMMWORD PTR [edi+96]
	movdqa xmm7, xmm2
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm4, XMMWORD PTR [edi+112]
	movdqa xmm7, xmm3
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+112], xmm4
	mov esi, edi
	add esi, 384
	mov eax, DWORD PTR [esp+8]
	sub eax, 1
27:
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm7
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm4
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm1, xmm2
	pxor xmm7, xmm1
	movdqu xmm0, XMMWORD PTR [edi+96]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm6
	movdqu xmm6, XMMWORD PTR [edi]
	pxor xmm6, xmm7
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	movdqu XMMWORD PTR [edi+80], xmm5
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu xmm3, XMMWORD PTR [edi]
	pxor xmm3, xmm0
	pxor xmm4, xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqa xmm6, xmm1
	pxor xmm6, xmm5
	movdqu XMMWORD PTR [edi+144], xmm1
	movdqa xmm1, xmm4
	pand xmm1, xmm3
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqa xmm3, xmm7
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm4
	movdqa xmm4, xmm5
	pand xmm4, xmm6
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+192], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm6, XMMWORD PTR [edi+16]
	pand xmm6, xmm7
	movdqu XMMWORD PTR [edi+224], xmm7
	movdqu xmm7, XMMWORD PTR [edi+64]
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm0
	pxor xmm7, xmm5
	pxor xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm3
	pxor xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm6
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+256], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm0
	pxor xmm7, xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	pand xmm3, xmm5
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm5, XMMWORD PTR [edi+176]
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+48]
	pand xmm4, xmm5
	pxor xmm4, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm0
	pxor xmm4, xmm3
	pxor xmm1, xmm6
	movdqa xmm6, xmm1
	pxor xmm6, xmm7
	movdqu xmm3, XMMWORD PTR [edi+144]
	pxor xmm4, xmm3
	movdqa xmm3, xmm4
	pand xmm3, xmm1
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqa xmm0, xmm2
	pxor xmm0, xmm3
	pxor xmm3, xmm7
	pand xmm0, xmm6
	pxor xmm0, xmm7
	pxor xmm4, xmm2
	movdqa xmm6, xmm3
	pxor xmm6, xmm0
	pand xmm7, xmm6
	pxor xmm1, xmm0
	pxor xmm1, xmm7
	pxor xmm7, xmm3
	pand xmm3, xmm4
	pxor xmm3, xmm2
	pand xmm7, xmm3
	pand xmm5, xmm1
	movdqu xmm2, XMMWORD PTR [edi+240]
	pand xmm2, xmm3
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pand xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [edi+48]
	pand xmm6, xmm1
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+176]
	pand xmm6, xmm4
	pxor xmm7, xmm5
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqa xmm7, xmm4
	pxor xmm7, xmm1
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm6, XMMWORD PTR [edi+160]
	pand xmm6, xmm4
	pxor xmm4, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu xmm6, XMMWORD PTR [edi]
	pand xmm6, xmm0
	pxor xmm2, xmm6
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm2, XMMWORD PTR [edi+96]
	pand xmm2, xmm4
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu xmm2, XMMWORD PTR [edi+144]
	pand xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [edi+16]
	pand xmm2, xmm1
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm0
	movdqu XMMWORD PTR [edi+192], xmm2
	movdqu xmm2, XMMWORD PTR [edi+208]
	pand xmm2, xmm0
	pxor xmm1, xmm4
	pxor xmm0, xmm7
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm0
	pxor xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [edi+256]
	pand xmm2, xmm7
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [edi+64]
	pand xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+80]
	pand xmm7, xmm2
	pxor xmm5, xmm0
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm2, xmm5
	pxor xmm3, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm1
	pxor xmm5, xmm6
	pxor xmm0, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	pxor xmm7, xmm5
	pxor xmm6, xmm1
	movdqu xmm1, XMMWORD PTR [edi+176]
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm2, xmm4
	pxor xmm3, xmm2
	pxor xmm0, xmm3
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi], xmm7
	movdqu xmm7, XMMWORD PTR [edi+208]
	pxor xmm7, xmm3
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+112], xmm4
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu XMMWORD PTR [edi+64], xmm7
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu XMMWORD PTR [edi+16], xmm6
	movdqu xmm6, XMMWORD PTR [edi+112]
	pshufd xmm5, xmm6, 250
	psrlq xmm5, 8
	pshufd xmm5, xmm5, 136
	punpcklqdq xmm6, xmm5
	pshuflw xmm6, xmm6, 180
	pshufhw xmm6, xmm6, 180
	pshufd xmm7, xmm6, 30
	pxor xmm6, xmm7
	pshufd xmm5, xmm6, 177
	pxor xmm7, xmm5
	movdqu xmm0, XMMWORD PTR [edi]
	pshufd xmm3, xmm0, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm0, xmm3
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshufd xmm2, xmm0, 30
	pxor xmm0, xmm2
	pshufd xmm3, xmm0, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm1, XMMWORD PTR [edi+16]
	pshufd xmm3, xmm1, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm1, xmm3
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	pshufd xmm2, xmm1, 30
	pxor xmm1, xmm2
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+16]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pshufd xmm3, xmm0, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm0, xmm3
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshufd xmm2, xmm0, 30
	pxor xmm0, xmm2
	pshufd xmm3, xmm0, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [esi+32]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [edi+48]
	pshufd xmm3, xmm1, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm1, xmm3
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	pshufd xmm2, xmm1, 30
	pxor xmm1, xmm2
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+48]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+48], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pshufd xmm3, xmm0, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm0, xmm3
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshufd xmm2, xmm0, 30
	pxor xmm0, xmm2
	pshufd xmm3, xmm0, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	pxor xmm2, xmm6
	movdqu xmm3, XMMWORD PTR [esi+64]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufd xmm3, xmm1, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm1, xmm3
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	pshufd xmm2, xmm1, 30
	pxor xmm1, xmm2
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [esi+80]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+80], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pshufd xmm3, xmm0, 250
	psrlq xmm3, 8
	pshufd xmm3, xmm3, 136
	punpcklqdq xmm0, xmm3
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshufd xmm2, xmm0, 30
	pxor xmm0, xmm2
	pshufd xmm3, xmm0, 177
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [esi+96]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+96], xmm2
	pxor xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [esi+112]
	pxor xmm7, xmm3
	movdqu XMMWORD PTR [edi+112], xmm7
	add esi, 128
	sub eax, 1
	jne 27b
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm7
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm4
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm1, xmm2
	pxor xmm7, xmm1
	movdqu xmm0, XMMWORD PTR [edi+96]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm6
	movdqu xmm6, XMMWORD PTR [edi]
	pxor xmm6, xmm7
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	movdqu XMMWORD PTR [edi+80], xmm5
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu xmm3, XMMWORD PTR [edi]
	pxor xmm3, xmm0
	pxor xmm4, xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqa xmm6, xmm1
	pxor xmm6, xmm5
	movdqu XMMWORD PTR [edi+144], xmm1
	movdqa xmm1, xmm4
	pand xmm1, xmm3
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqa xmm3, xmm7
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm4
	movdqa xmm4, xmm5
	pand xmm4, xmm6
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+192], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm6, XMMWORD PTR [edi+16]
	pand xmm6, xmm7
	movdqu XMMWORD PTR [edi+224], xmm7
	movdqu xmm7, XMMWORD PTR [edi+64]
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm0
	pxor xmm7, xmm5
	pxor xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm3
	pxor xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm6
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+256], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm0
	pxor xmm7, xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	pand xmm3, xmm5
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm5, XMMWORD PTR [edi+176]
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+48]
	pand xmm4, xmm5
	pxor xmm4, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm0
	pxor xmm4, xmm3
	pxor xmm1, xmm6
	movdqa xmm6, xmm1
	pxor xmm6, xmm7
	movdqu xmm3, XMMWORD PTR [edi+144]
	pxor xmm4, xmm3
	movdqa xmm3, xmm4
	pand xmm3, xmm1
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqa xmm0, xmm2
	pxor xmm0, xmm3
	pxor xmm3, xmm7
	pand xmm0, xmm6
	pxor xmm0, xmm7
	pxor xmm4, xmm2
	movdqa xmm6, xmm3
	pxor xmm6, xmm0
	pand xmm7, xmm6
	pxor xmm1, xmm0
	pxor xmm1, xmm7
	pxor xmm7, xmm3
	pand xmm3, xmm4
	pxor xmm3, xmm2
	pand xmm7, xmm3
	pand xmm5, xmm1
	movdqu xmm2, XMMWORD PTR [edi+240]
	pand xmm2, xmm3
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pand xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [edi+48]
	pand xmm6, xmm1
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+176]
	pand xmm6, xmm4
	pxor xmm7, xmm5
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqa xmm7, xmm4
	pxor xmm7, xmm1
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm6, XMMWORD PTR [edi+160]
	pand xmm6, xmm4
	pxor xmm4, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu xmm6, XMMWORD PTR [edi]
	pand xmm6, xmm0
	pxor xmm2, xmm6
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm2, XMMWORD PTR [edi+96]
	pand xmm2, xmm4
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu xmm2, XMMWORD PTR [edi+144]
	pand xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [edi+16]
	pand xmm2, xmm1
	pxor xmm2, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm0
	movdqu XMMWORD PTR [edi+192], xmm2
	movdqu xmm2, XMMWORD PTR [edi+208]
	pand xmm2, xmm0
	pxor xmm1, xmm4
	pxor xmm0, xmm7
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm0
	pxor xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [edi+256]
	pand xmm2, xmm7
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [edi+64]
	pand xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+80]
	pand xmm7, xmm2
	pxor xmm5, xmm0
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm2, xmm5
	pxor xmm3, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm1
	pxor xmm5, xmm6
	pxor xmm0, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	pxor xmm7, xmm5
	pxor xmm6, xmm1
	movdqu xmm1, XMMWORD PTR [edi+176]
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm2, xmm4
	pxor xmm3, xmm2
	pxor xmm0, xmm3
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi], xmm7
	movdqu xmm7, XMMWORD PTR [edi+208]
	pxor xmm7, xmm3
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+112], xmm4
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu XMMWORD PTR [edi+64], xmm7
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu XMMWORD PTR [edi+16], xmm6
	mov eax, DWORD PTR [esp+8]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add ecx, eax
	movdqu xmm0, XMMWORD PTR [edi+64]
	pshufd xmm7, xmm0, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm0, xmm7
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufd xmm7, xmm1, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm1, xmm7
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqu xmm2, XMMWORD PTR [edi+96]
	pshufd xmm7, xmm2, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm2, xmm7
	pshuflw xmm2, xmm2, 180
	pshufhw xmm2, xmm2, 180
	movdqu xmm3, XMMWORD PTR [edi+112]
	pshufd xmm7, xmm3, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm3, xmm7
	pshuflw xmm3, xmm3, 180
	pshufhw xmm3, xmm3, 180
	mov eax, 1431655765
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 1
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 1
	pxor xmm0, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 1
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 1
	pxor xmm2, xmm7
	mov eax, 858993459
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 2
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm0, xmm7
	movdqa xmm7, xmm1
	psrlq xmm7, 2
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 2
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+112], xmm3
	movdqu xmm0, XMMWORD PTR [edi]
	pshufd xmm7, xmm0, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm0, xmm7
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	movdqu xmm1, XMMWORD PTR [edi+16]
	pshufd xmm7, xmm1, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm1, xmm7
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqu xmm2, XMMWORD PTR [edi+32]
	pshufd xmm7, xmm2, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm2, xmm7
	pshuflw xmm2, xmm2, 180
	pshufhw xmm2, xmm2, 180
	movdqu xmm3, XMMWORD PTR [edi+48]
	pshufd xmm7, xmm3, 250
	psrlq xmm7, 8
	pshufd xmm7, xmm7, 136
	punpcklqdq xmm3, xmm7
	pshuflw xmm3, xmm3, 180
	pshufhw xmm3, xmm3, 180
	mov eax, 1431655765
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 1
	pxor xmm7, xmm1
	pand xmm7, xmm6
	pxor xmm1, xmm7
	psllq xmm7, 1
	pxor xmm0, xmm7
	movdqa xmm7, xmm2
	psrlq xmm7, 1
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 1
	pxor xmm2, xmm7
	mov eax, 858993459
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqa xmm7, xmm0
	psrlq xmm7, 2
	pxor xmm7, xmm2
	pand xmm7, xmm6
	pxor xmm2, xmm7
	psllq xmm7, 2
	pxor xmm0, xmm7
	movdqa xmm7, xmm1
	psrlq xmm7, 2
	pxor xmm7, xmm3
	pand xmm7, xmm6
	pxor xmm3, xmm7
	psllq xmm7, 2
	pxor xmm1, xmm7
	mov eax, 252645135
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm7, xmm0
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm7, xmm1
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+16], xmm1
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm4, XMMWORD PTR [edi+96]
	movdqa xmm7, xmm2
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm4, XMMWORD PTR [edi+112]
	movdqa xmm7, xmm3
	psrlq xmm7, 4
	pxor xmm7, xmm4
	pand xmm7, xmm6
	pxor xmm4, xmm7
	psllq xmm7, 4
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+112], xmm4
	movdqu xmm5, XMMWORD PTR [ecx]
	mov eax, 1667457891
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	pxor xmm5, xmm7
	mov eax, -16711936
	movd xmm6, eax
	punpcklqdq xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [edi]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi], xmm0
	movdqu xmm0, XMMWORD PTR [edi+16]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+32]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+48]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+64]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm0, XMMWORD PTR [edi+80]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+96]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+112]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqa xmm7, xmm0
	psrlq xmm7, 24
	pxor xmm7, xmm0
	pand xmm7, xmm6
	pxor xmm0, xmm7
	psllq xmm7, 24
	pxor xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	mov edx, edi
	cmp ebp, 8
	jae 28f
	mov ecx, ebp
	jmp 29f
28:
	mov ecx, 8
29:
	sub ebp, ecx
210:
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu XMMWORD PTR [ebx], xmm0
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 210b
	test ebp, ebp
	jne 23b
	jmp 22f
21:
22:
	mov ebx, DWORD PTR [edi+272]
	mov esi, DWORD PTR [edi+276]
	mov ebp, DWORD PTR [edi+284]
	mov edi, DWORD PTR [edi+280]
	ret
	.p2align 6
