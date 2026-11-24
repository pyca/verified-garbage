// The functions of `src/internal/vg_rc2_expand_key_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key_ssse3:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov ebp, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+16]
	mov ecx, 0
20:
	mov edx, ebp
	add edx, ecx
	movzx eax, BYTE PTR [edx]
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	add ecx, 1
	cmp ecx, esi
	jne 20b
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_RC2_PITABLE}
	pop ecx
	mov ebp, eax
	mov ecx, esi
	cmp ecx, 128
	jne 21f
	jmp 22f
21:
23:
	mov edx, edi
	add edx, ecx
	sub edx, 1
	movzx eax, BYTE PTR [edx]
	mov ebx, ecx
	sub ebx, esi
	mov edx, edi
	add edx, ebx
	movzx ebx, BYTE PTR [edx]
	add eax, ebx
	mov ebx, eax
	shr ebx, 4
	and ebx, 15
	movd xmm5, ebx
	and eax, 15
	or eax, -2139062272
	movd xmm6, eax
	ror eax, 24
	movd xmm7, eax
	movdqu xmm1, XMMWORD PTR [ebp]
	pshufb xmm1, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+16]
	pshufb xmm0, xmm7
	por xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebp+32]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+48]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	punpcklwd xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+64]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+80]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+96]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+112]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	punpckldq xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+128]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+144]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+160]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+176]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebp+192]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+208]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebp+224]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+240]
	pshufb xmm0, xmm7
	por xmm4, xmm0
	punpcklwd xmm3, xmm4
	punpckldq xmm2, xmm3
	punpcklqdq xmm1, xmm2
	pshufb xmm1, xmm5
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	add ecx, 1
	cmp ecx, 128
	jne 23b
22:
	mov esi, DWORD PTR [esp+12]
	add esi, 7
	shr esi, 3
	mov ecx, 128
	sub ecx, esi
	mov edx, DWORD PTR [esp+12]
	and edx, 7
	mov ebx, 255
	cmp edx, 1
	je 24f
	jmp 25f
24:
	mov ebx, 1
25:
	cmp edx, 2
	je 26f
	jmp 27f
26:
	mov ebx, 3
27:
	cmp edx, 3
	je 28f
	jmp 29f
28:
	mov ebx, 7
29:
	cmp edx, 4
	je 210f
	jmp 211f
210:
	mov ebx, 15
211:
	cmp edx, 5
	je 212f
	jmp 213f
212:
	mov ebx, 31
213:
	cmp edx, 6
	je 214f
	jmp 215f
214:
	mov ebx, 63
215:
	cmp edx, 7
	je 216f
	jmp 217f
216:
	mov ebx, 127
217:
	mov edx, edi
	add edx, ecx
	movzx eax, BYTE PTR [edx]
	and eax, ebx
	mov ebx, eax
	shr ebx, 4
	and ebx, 15
	movd xmm5, ebx
	and eax, 15
	or eax, -2139062272
	movd xmm6, eax
	ror eax, 24
	movd xmm7, eax
	movdqu xmm1, XMMWORD PTR [ebp]
	pshufb xmm1, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+16]
	pshufb xmm0, xmm7
	por xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebp+32]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+48]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	punpcklwd xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+64]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+80]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+96]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+112]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	punpckldq xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+128]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+144]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+160]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+176]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebp+192]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+208]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebp+224]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+240]
	pshufb xmm0, xmm7
	por xmm4, xmm0
	punpcklwd xmm3, xmm4
	punpckldq xmm2, xmm3
	punpcklqdq xmm1, xmm2
	pshufb xmm1, xmm5
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	cmp ecx, 0
	jne 218f
	jmp 219f
218:
220:
	sub ecx, 1
	mov edx, edi
	add edx, ecx
	add edx, 1
	movzx eax, BYTE PTR [edx]
	mov ebx, ecx
	add ebx, esi
	mov edx, edi
	add edx, ebx
	movzx ebx, BYTE PTR [edx]
	xor eax, ebx
	mov ebx, eax
	shr ebx, 4
	and ebx, 15
	movd xmm5, ebx
	and eax, 15
	or eax, -2139062272
	movd xmm6, eax
	ror eax, 24
	movd xmm7, eax
	movdqu xmm1, XMMWORD PTR [ebp]
	pshufb xmm1, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+16]
	pshufb xmm0, xmm7
	por xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebp+32]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+48]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	punpcklwd xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+64]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+80]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+96]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+112]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	punpckldq xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebp+128]
	pshufb xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+144]
	pshufb xmm0, xmm7
	por xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebp+160]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+176]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	punpcklwd xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebp+192]
	pshufb xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+208]
	pshufb xmm0, xmm7
	por xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebp+224]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebp+240]
	pshufb xmm0, xmm7
	por xmm4, xmm0
	punpcklwd xmm3, xmm4
	punpckldq xmm2, xmm3
	punpcklqdq xmm1, xmm2
	pshufb xmm1, xmm5
	movdqu xmm7, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm1
	mov eax, DWORD PTR [edi]
	movdqu XMMWORD PTR [edi], xmm7
	and eax, 255
	mov edx, edi
	add edx, ecx
	mov BYTE PTR [edx], al
	cmp ecx, 0
	jne 220b
219:
	mov eax, DWORD PTR [esp+20]
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	ret
	.p2align 6
